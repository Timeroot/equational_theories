import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_pyx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq74 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq74 x y
       grind)
    | exact superpose eq74 eq44
    | (have j1 := eq74 x y
       grind)
    | exact resolve eq44 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98
    | exact resolve eq98 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq106
    | exact resolve eq106 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq554 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq108 eq74
    | (have j0 := eq74 (σ x) (σ y)
       grind)
    | exact resolve eq74 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq555 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq554
    | exact resolve eq554 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq558 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq555
       have r₂ := eq27
       grind)
    | exact resolve eq555 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq580 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  have eq587 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq558 eq14
    | exact resolve eq14 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq853 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq587 sF3
       have i₂ := eq580 sF3
       grind)
    | exact superpose eq580 eq587
    | exact resolve eq587 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq875 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq853 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq853
       grind)
    | exact resolve eq13 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq876 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq875 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875
  have eq934 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq876 eq108
    | exact resolve eq108 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq876
  have eq939 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq934
  have eq945 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq939
    | exact resolve eq939 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939
  have eq947 : y = (M.op y x) := by
    first
    | (have r₁ := eq945
       have r₂ := eq27
       grind)
    | exact resolve eq945 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq950 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq947
       grind)
    | exact superpose eq947 eq14
    | exact resolve eq14 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq951 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq947
       grind)
    | exact superpose eq947 eq14
    | exact resolve eq14 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq970 : x = (M.op (M.op y y) x) := by
    first
    | (have i₁ := eq950 x
       have i₂ := eq947
       grind)
    | exact superpose eq947 eq950
    | exact resolve eq950 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq996 : y = (M.op y y) := by
    first
    | (have i₁ := eq951 y
       have i₂ := eq580 y
       grind)
    | exact superpose eq580 eq951
    | exact resolve eq951 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580 eq951
  have eq1019 : x = (M.op y x) := by
    first
    | (have i₁ := eq970
       have i₂ := eq996
       grind)
    | exact superpose eq996 eq970
    | exact resolve eq970 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq1031 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq996
       grind)
    | exact superpose eq996 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq996
       grind)
    | exact resolve eq13 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq1032 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1031 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031
  have eq1033 : x = y := by
    first
    | (have i₁ := eq1019
       have i₂ := eq947
       grind)
    | exact superpose eq947 eq1019
    | exact resolve eq1019 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019
  have eq1034 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1033
       grind)
    | exact superpose eq1033 eq18
    | exact resolve eq18 eq1033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1035 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1033
       grind)
    | exact superpose eq1033 eq24
    | exact resolve eq24 eq1033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1051 : x = (M.op x x) := by
    first
    | (have i₁ := eq947
       have i₂ := eq1033
       grind)
    | exact superpose eq1033 eq947
    | exact resolve eq947 eq1033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq1064 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1035
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1035
    | exact resolve eq1035 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035
  have eq1065 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1064 eq26
    | exact resolve eq26 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1064
  have eq1116 : x = (M.op x y) := by
    first
    | (have i₁ := eq1051
       have i₂ := eq1034
       grind)
    | exact superpose eq1034 eq1051
    | exact resolve eq1051 eq1034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051
  have eq1117 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1116 eq20
    | exact resolve eq20 eq1116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq1146 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1117
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1117
    | exact resolve eq1117 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1117
  have eq1212 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1146 eq1065
    | exact resolve eq1065 eq1146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065
  have eq1249 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq1032 X0
       have i₂ := eq1033
       grind)
    | exact superpose eq1033 eq1032
    | exact resolve eq1032 eq1033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032 eq1033
  have eq1253 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq1249 x
       grind)
    | exact superpose eq1249 eq43
    | exact resolve eq43 eq1249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq1249
  have eq1261 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1253
       have i₂ := eq1034
       grind)
    | exact superpose eq1034 eq1253
    | exact resolve eq1253 eq1034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034 eq1253
  have eq1267 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1146 eq1261
    | exact resolve eq1261 eq1146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146 eq1261
  have eq1270 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq1267
    | exact resolve eq1267 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1267
  have eq1278 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1270 eq74
    | (have j0 := eq74 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq74 eq1270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq1270
  have eq1279 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq1278
  have eq1281 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1212 eq1279
    | exact resolve eq1279 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212 eq1279
  have eq1284 : False := by grind
  exact eq1284

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyy_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
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
  have eq41 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) ≠ X0 ∨ (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op (M.op (M.op X1 X0) (M.op X1 X2)) (M.op (M.op X1 X0) (M.op X1 X2))) ∨ (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j1 := eq14 X2 X0
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
  have eq58 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = X1 ∨ (M.op (M.op X0 X1) X2) = (k X2 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0 X1
       have i₂ := eq14 X2 (M.op X0 X1)
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X2 (M.op X0 X1)
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq57 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq84 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  have eq94 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq84 X0
       grind)
    | exact superpose eq84 eq9
    | exact resolve eq9 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq150 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (k X2 (τ X0)) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq64 (τ X0) X2 X1
       grind)
    | exact superpose eq64 eq18
    | (have j1 := eq64 (τ X0) X2 X1
       grind)
    | exact resolve eq18 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq64
  have eq163 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq94
    | exact resolve eq94 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq222 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X2
       have i₂ := eq163 X0 X1
       grind)
    | exact superpose eq163 eq9
    | exact resolve eq9 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) (M.op X0 X1)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 (M.op X0 X1) X0 X2 X3
       have i₂ := eq163 X0 X1
       grind)
    | exact superpose eq163 eq24
    | exact resolve eq24 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq313 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq59 x y
       grind)
    | exact superpose eq59 eq16
    | (have j1 := eq59 x x
       grind)
    | exact resolve eq16 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq59 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq346 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq344 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq542 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op (M.op X0 (M.op X0 X1)) X2) = (k X2 (M.op X0 (M.op X0 X1))) ∨ (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41 (M.op X0 X2) X0 X2
       have i₂ := eq58 X0 (M.op X0 X2) X2
       grind)
    | exact superpose eq58 eq41
    | (have j1 := eq58 X0 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq41 (M.op X0 X2) X0 X2
       have r₂ := eq58 X0 (M.op X0 X2) X2
       grind)
    | exact resolve eq41 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq58
  have eq544 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op (M.op X0 (M.op X0 X1)) X2) = (k X2 (M.op X0 (M.op X0 X1))) ∨ (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq542 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq545 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op (M.op X0 (M.op X0 X1)) X2) = (k X2 (M.op X0 (M.op X0 X1))) ∨ (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq544 X0 X1 X2
       have j1 := eq12 (M.op X0 X1) (M.op X0 X1)
       grind)
    | (have r₁ := eq544 X0 X1 X2
       have r₂ := eq12 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq544 X0 X1 (M.op X0 (M.op X0 X1))
       have r₂ := eq12 X0 (M.op X0 (M.op X0 X1))
       grind)
    | exact resolve eq544 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq561 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k X2 (M.op X0 X1)) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq545 X0 X1 X2
       have i₂ := eq163 X0 X1
       grind)
    | exact superpose eq163 eq545
    | (have j0 := eq545 X0 X1 X2
       grind)
    | exact resolve eq545 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq566 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k X2 (M.op X0 X1)) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq561 X0 X1 X2
       have i₂ := eq163 X0 X1
       grind)
    | exact superpose eq163 eq561
    | (have j0 := eq561 X0 X1 X2
       grind)
    | exact resolve eq561 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq5264 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq346 (τ X0)
       have i₂ := eq150 X0 X1 (τ X0)
       grind)
    | exact superpose eq150 eq346
    | (have j0 := eq346 (τ X0)
       have j1 := eq150 X0 X1 x
       grind)
    | exact resolve eq346 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq346
  have eq5288 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq5264 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5264
  have eq5309 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5288 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5288
    | (have j0 := eq5288 X0 X1
       grind)
    | exact resolve eq5288 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5288
  have eq26518 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq566 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq26519 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq26518 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26518
  have eq26538 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq26519 X0 X1
       have j1 := eq12 (M.op X0 X1) (M.op X0 X1)
       grind)
    | (have r₁ := eq26519 X0 X1
       have r₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact resolve eq26519 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26519
  have eq26636 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq26538 (M.op (M.op (M.op (M.op X0 x) (M.op X0 x)) x) (M.op X0 x)) x
       have i₂ := eq227 X0 x x x
       grind)
    | exact superpose eq227 eq26538
    | exact resolve eq26538 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq26538
  have eq27117 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq345 X0 X0
       have i₂ := eq26636 X0
       grind)
    | exact superpose eq26636 eq345
    | (have j0 := eq345 X0 X0
       grind)
    | exact resolve eq345 eq26636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq27146 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq26636 (σ X0)
       grind)
    | exact superpose eq26636 eq15
    | exact resolve eq15 eq26636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27154 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq26636 (τ X0)
       grind)
    | exact superpose eq26636 eq33
    | exact resolve eq33 eq26636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq27176 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq27117 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27117
  have eq27202 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq27154 X0
       have i₂ := eq26636 X0
       grind)
    | exact superpose eq26636 eq27154
    | exact resolve eq27154 eq26636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27154
  have eq27209 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq27146 X0
       have i₂ := eq26636 X0
       grind)
    | exact superpose eq26636 eq27146
    | exact resolve eq27146 eq26636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26636 eq27146
  have eq27548 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ X0) X1) (τ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ X0)
       have i₂ := eq27202 X0
       grind)
    | exact superpose eq27202 eq9
    | exact resolve eq9 eq27202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27202
  have eq28335 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq27209 X0
       grind)
    | exact superpose eq27209 eq9
    | exact resolve eq9 eq27209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35883 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (σ X0)) X1) (σ (σ (M.op X0 X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28335 (σ X0) X1
       have i₂ := eq27209 X0
       grind)
    | exact superpose eq27209 eq28335
    | exact resolve eq28335 eq27209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28335
  have eq60345 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (σ X1) (σ X0)) = (σ (M.op (τ (σ X0)) X1)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq27209 X0
       have i₂ := eq5309 (σ X0) X1
       grind)
    | exact superpose eq5309 eq27209
    | (have j1 := eq5309 (σ X0) X1
       grind)
    | exact resolve eq27209 eq5309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5309
  have eq60536 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq60345 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq60345
    | (have j0 := eq60345 X0 X1
       grind)
    | exact resolve eq60345 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60345
  have eq60641 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq60536 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq60536
    | (have j0 := eq60536 X0 X1
       grind)
    | exact resolve eq60536 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60536
  have eq60670 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq60641 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq60641
    | (have j0 := eq60641 X0 X1
       grind)
    | exact resolve eq60641 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60641
  have eq458678 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq313
       have i₂ := eq60670 x y
       grind)
    | exact superpose eq60670 eq313
    | (have j1 := eq60670 x y
       grind)
    | (have r₁ := eq313
       have r₂ := eq60670 x y
       grind)
    | exact resolve eq313 eq60670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313 eq60670
  have eq459288 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by grind
  clear eq458678
  have eq459378 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq27176 x
       grind)
    | (have r₁ := eq459288
       have r₂ := eq27176 x
       grind)
    | exact resolve eq459288 eq27176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459288
  have eq459491 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq459378
       have i₂ := eq27209 x
       grind)
    | exact superpose eq27209 eq459378
    | exact resolve eq459378 eq27209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459378
  have eq462114 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq163 (σ x) (σ y)
       have i₂ := eq459491
       grind)
    | exact superpose eq459491 eq163
    | exact resolve eq163 eq459491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459491
  have eq462449 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq27176 x
       grind)
    | (have r₁ := eq462114
       have r₂ := eq27176 x
       grind)
    | exact resolve eq462114 eq27176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27176 eq462114
  have eq462530 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq462449
       have i₂ := eq27209 x
       grind)
    | exact superpose eq27209 eq462449
    | exact resolve eq462449 eq27209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27209 eq462449
  have eq464474 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq462530
       grind)
    | exact superpose eq462530 eq10
    | exact resolve eq10 eq462530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462530
  have eq464773 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq464474
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq464474
    | exact resolve eq464474 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464474
  have eq466561 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq163 x y
       have i₂ := eq464773
       grind)
    | exact superpose eq464773 eq163
    | exact resolve eq163 eq464773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464773
  have eq466804 : x = (M.op x x) := by grind
  clear eq466561
  have eq470530 : ∀ X0 : G, (M.op (M.op (M.op (τ x) X0) (τ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq27548 x X0
       have i₂ := eq466804
       grind)
    | exact superpose eq466804 eq27548
    | exact resolve eq27548 eq466804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27548
  have eq470637 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq466804
       grind)
    | exact superpose eq466804 eq9
    | exact resolve eq9 eq466804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470718 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq222 x x x
       have i₂ := eq466804
       grind)
    | exact superpose eq466804 eq222
    | exact resolve eq222 eq466804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466804
  have eq470992 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq470718 X0
       have i₂ := eq163 x X0
       grind)
    | exact superpose eq163 eq470718
    | exact resolve eq470718 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq470718
  have eq491596 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq470637 X0
       have i₂ := eq470992 X0
       grind)
    | exact superpose eq470992 eq470637
    | exact resolve eq470637 eq470992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491864 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) x) X1) = (M.op (M.op (M.op (M.op (M.op x X0) x) X1) X0) (M.op (M.op (M.op x X0) x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq222 (M.op (M.op x X0) x) X1 X0
       have i₂ := eq470637 X0
       grind)
    | exact superpose eq470637 eq222
    | exact resolve eq222 eq470637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq470637
  have eq492295 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq491864 X0 X1
       have i₂ := eq470992 X0
       grind)
    | exact superpose eq470992 eq491864
    | exact resolve eq491864 eq470992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470992 eq491864
  have eq492492 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq492295 X0 X0
       have i₂ := eq491596 X0
       grind)
    | exact superpose eq491596 eq492295
    | exact resolve eq492295 eq491596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492295
  have eq542068 : ∀ X0 : G, (M.op (τ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq470530 X0
       have i₂ := eq492492 X0 (τ x)
       grind)
    | exact superpose eq492492 eq470530
    | exact resolve eq470530 eq492492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470530
  have eq546314 : ∀ X0 : G, (M.op (M.op (M.op (σ (σ (τ x))) X0) (σ (σ (τ x)))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq35883 (τ x) X0
       have i₂ := eq542068 (τ x)
       grind)
    | exact superpose eq542068 eq35883
    | exact resolve eq35883 eq542068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35883 eq542068
  have eq547097 : ∀ X0 : G, (M.op (σ (σ (τ x))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq546314 X0
       have i₂ := eq492492 X0 (σ (σ (τ x)))
       grind)
    | exact superpose eq492492 eq546314
    | exact resolve eq546314 eq492492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492492 eq546314
  have eq547176 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq547097 X0
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq547097
    | exact resolve eq547097 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547097
  have eq550993 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq547176 (σ y)
       grind)
    | exact superpose eq547176 eq16
    | exact resolve eq16 eq547176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547176
  have eq551938 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq550993
       have i₂ := eq491596 y
       grind)
    | exact superpose eq491596 eq550993
    | exact resolve eq550993 eq491596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491596 eq550993
  have eq551939 : False := by grind
  exact eq551939

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pxy_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
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
  clear eq23
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq12 (σ X0) X1
       grind)
    | exact superpose eq12 eq29
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq29 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq79 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
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
  have eq82 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq83 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq29
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq62 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq96 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq9
    | exact resolve eq9 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq9
    | exact resolve eq9 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq96
    | exact resolve eq96 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq90 (σ X0)
       have i₂ := eq66 X0 X0
       grind)
    | exact superpose eq66 eq90
    | (have j1 := eq66 X0 X0
       grind)
    | exact resolve eq90 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq588 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq82 x y
       grind)
    | exact superpose eq82 eq16
    | (have j1 := eq82 x y
       grind)
    | exact resolve eq16 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq90 (σ X0)
       have i₂ := eq82 X0 X0
       grind)
    | exact superpose eq82 eq90
    | (have j1 := eq82 X0 X0
       grind)
    | exact resolve eq90 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq605 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq607 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq82 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq608 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq607 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq610 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq605 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq611 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq604 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq614 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq610 X0
       have j1 := eq608 X0
       grind)
    | (have r₁ := eq610 X0
       have r₂ := eq608 X0
       grind)
    | exact resolve eq610 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq615 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq611 X0
       have j1 := eq272 X0
       grind)
    | (have r₁ := eq611 X0
       have r₂ := eq272 X0
       grind)
    | exact resolve eq611 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272 eq611
  have eq621 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq614 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq614
    | (have j0 := eq614 X0
       grind)
    | exact resolve eq614 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq623 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq615 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq615
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq615 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq624 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq615 X0
       have i₂ := eq12 X0 X0
       grind)
    | exact superpose eq12 eq615
    | (have j1 := eq12 X0 X0
       grind)
    | exact resolve eq615 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq625 : ∀ X0 : G, (σ (σ X0)) = (M.op (σ (σ (k X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq615 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq615
    | exact resolve eq615 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq628 : ∀ X0 : G, (σ (τ X0)) = (M.op (k (σ (τ X0)) X0) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq615 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq615
    | exact resolve eq615 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq649 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq623 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq654 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq628 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq628
    | exact resolve eq628 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq657 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq649 X0
       have j1 := eq624 X0
       grind)
    | (have r₁ := eq649 X0
       have r₂ := eq624 X0
       grind)
    | exact resolve eq649 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624 eq649
  have eq663 : ∀ X0 : G, (τ X0) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq654 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq654
    | exact resolve eq654 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq705 : ∀ X0 : G, (τ (τ X0)) = (M.op (τ (τ (k X0 X0))) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq663 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq663
    | exact resolve eq663 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq916 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k (τ X0) (τ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq608 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq608
    | exact resolve eq608 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq924 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (σ X0) ≠ (σ X0) ∨ (σ X0) ≠ (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq67 X0 (σ X0)
       have i₂ := eq608 X0
       grind)
    | exact superpose eq608 eq67
    | (have j1 := eq608 X0
       grind)
    | (have r₁ := eq67 X0 (σ X0)
       have r₂ := eq608 X0
       grind)
    | exact resolve eq67 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq942 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (σ X0) ≠ (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq924 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq950 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq942 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq942
    | (have j0 := eq942 X0
       grind)
    | exact resolve eq942 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq954 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq916 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq916
    | (have j0 := eq916 X0
       grind)
    | exact resolve eq916 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq955 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq954 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq954
    | (have j0 := eq954 X0
       grind)
    | exact resolve eq954 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq970 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = X1 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 X1
       have i₂ := eq955 X0
       grind)
    | exact superpose eq955 eq96
    | (have j1 := eq955 X0
       grind)
    | exact resolve eq96 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq971 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = X0 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 X1
       have i₂ := eq955 X0
       grind)
    | exact superpose eq955 eq97
    | (have j1 := eq955 X0
       grind)
    | exact resolve eq97 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq972 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq657 X0
       have i₂ := eq955 X0
       grind)
    | exact superpose eq955 eq657
    | (have j1 := eq955 (σ X0)
       grind)
    | exact resolve eq657 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq988 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ X0))) ∨ (τ X0) ≠ (τ X0) ∨ (τ X0) ≠ (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0 (τ X0)
       have i₂ := eq955 (τ X0)
       grind)
    | exact superpose eq955 eq68
    | (have j1 := eq955 (τ X0)
       grind)
    | (have r₁ := eq68 X0 X0
       have r₂ := eq955 X0
       grind)
    | exact resolve eq68 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq991 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ X0))) ∨ (τ X0) ≠ (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq988 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq996 : ∀ X0 : G, (k X0 X0) = X0 ∨ (τ X0) ≠ (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq991 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq991
    | (have j0 := eq991 X0
       grind)
    | exact resolve eq991 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991
  have eq1005 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq971 X0 X1
       have i₂ := eq109 X0 X1
       grind)
    | exact superpose eq109 eq971
    | (have j0 := eq971 X0 X1
       grind)
    | exact resolve eq971 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971
  have eq1011 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq996 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq996
    | (have j0 := eq996 X0
       grind)
    | exact resolve eq996 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq1022 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq950 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq950
    | (have j0 := eq950 (τ X0)
       grind)
    | exact resolve eq950 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq1024 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1022 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1022
    | (have j0 := eq1022 X0
       grind)
    | exact resolve eq1022 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq1027 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq1024 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq1024
    | (have j0 := eq1024 X0
       grind)
    | exact resolve eq1024 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq1089 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1011 (σ X0)
       have i₂ := eq29 X0 (σ X0)
       grind)
    | exact superpose eq29 eq1011
    | (have j0 := eq1011 (σ X0)
       grind)
    | exact resolve eq1011 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq1095 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1089 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1089
    | (have j0 := eq1089 X0
       grind)
    | exact resolve eq1089 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089
  have eq1100 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq1095 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1095
    | (have j0 := eq1095 X0
       grind)
    | exact resolve eq1095 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095
  have eq1108 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq1027 x
       have i₂ := eq12 x x
       grind)
    | exact superpose eq12 eq1027
    | (have j1 := eq12 X0 X0
       grind)
    | exact resolve eq1027 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027
  have eq1134 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have j0 := eq1108 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108
  have eq1172 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq1100 x
       have i₂ := eq12 x x
       grind)
    | exact superpose eq12 eq1100
    | (have j1 := eq12 X0 X0
       grind)
    | exact resolve eq1100 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1183 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (k (k X0 X0) X1)) ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 X0) X1
       have i₂ := eq1100 X0
       grind)
    | exact superpose eq1100 eq15
    | (have j1 := eq1100 X0
       grind)
    | exact resolve eq15 eq1100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100
  have eq1209 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have j0 := eq1172 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq1231 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (k (k X0 X0) X1)) ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1183 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1183
    | (have j0 := eq1183 X0 X1
       grind)
    | exact resolve eq1183 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183
  have eq1269 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq67 X0 (σ X0)
       have i₂ := eq1134 (σ X0)
       grind)
    | exact superpose eq1134 eq67
    | (have j0 := eq67 X0 (σ X0)
       have j1 := eq1134 (σ X0)
       grind)
    | exact resolve eq67 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq1275 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 (M.op X0 X0))) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq32 (M.op X0 X0) X1
       have i₂ := eq1134 X0
       grind)
    | exact superpose eq1134 eq32
    | (have j1 := eq1134 X0
       grind)
    | exact resolve eq32 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1276 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k (M.op X0 X0) X1)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 (M.op X0 X0)
       have i₂ := eq1134 X0
       grind)
    | exact superpose eq1134 eq32
    | (have j1 := eq1134 X0
       grind)
    | exact resolve eq32 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1281 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (σ X0) ≠ (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1269 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1269
  have eq1285 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (k (M.op X0 X0) X1)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1276 X0 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq1276
    | (have j0 := eq1276 X0 X1
       grind)
    | exact resolve eq1276 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276
  have eq1286 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (k X1 (M.op X0 X0))) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1275 X0 X1
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq1275
    | (have j0 := eq1275 X0 X1
       grind)
    | exact resolve eq1275 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1275
  have eq1290 : ∀ X0 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1281 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1281
    | (have j0 := eq1281 X0
       grind)
    | exact resolve eq1281 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281
  have eq1294 : ∀ X0 X1 : G, (τ (k X1 (M.op X0 X0))) = (τ (M.op X1 X0)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | exact superpose eq12 eq1286
    | (have j0 := eq1286 X0 X1
       have j1 := eq12 X0 X0
       grind)
    | exact resolve eq1286 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286
  have eq1328 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq657 X0
       have i₂ := eq1209 X0
       grind)
    | exact superpose eq1209 eq657
    | (have j1 := eq1209 X0
       grind)
    | exact resolve eq657 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq1330 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (k (M.op X0 X0) X1)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 (M.op X0 X0) X1
       have i₂ := eq1209 X0
       grind)
    | exact superpose eq1209 eq15
    | (have j1 := eq1209 X0
       grind)
    | exact resolve eq15 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1331 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (k X1 (M.op X0 X0))) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (M.op X0 X0)
       have i₂ := eq1209 X0
       grind)
    | exact superpose eq1209 eq15
    | (have j1 := eq1209 X0
       grind)
    | exact resolve eq15 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1378 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (k X1 (M.op X0 X0))) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1331 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1331
    | (have j0 := eq1331 X0 X1
       grind)
    | exact resolve eq1331 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1331
  have eq1379 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (k (M.op X0 X0) X1)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1330 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1330
    | (have j0 := eq1330 X0 X1
       grind)
    | exact resolve eq1330 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1330
  have eq1393 : ∀ X0 X1 : G, (σ (k X1 (M.op X0 X0))) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | exact superpose eq12 eq1378
    | (have j0 := eq1378 X0 X1
       have j1 := eq12 X0 X0
       grind)
    | exact resolve eq1378 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378
  have eq1407 : ∀ X0 : G, (σ (σ X0)) = (M.op (σ (σ (M.op X0 X0))) (σ (σ X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq625 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq625
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq625 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1419 : ∀ X0 : G, (σ (σ X0)) = (M.op (σ (σ (k (M.op X0 X0) (M.op X0 X0)))) (σ (σ X0))) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq625 (M.op X0 X0)
       have i₂ := eq1209 X0
       grind)
    | exact superpose eq1209 eq625
    | (have j1 := eq1209 X0
       grind)
    | exact resolve eq625 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq1437 : ∀ X0 : G, (σ (σ X0)) = (M.op (σ (σ (M.op X0 X0))) (σ (σ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1407 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407
  have eq1444 : ∀ X0 : G, (σ (σ X0)) = (M.op (σ (σ (k X0 (M.op X0 X0)))) (σ (σ X0))) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | exact superpose eq1379 eq1419
    | (have j0 := eq1419 X0
       have j1 := eq1379 X0 x
       grind)
    | exact resolve eq1419 eq1379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1379 eq1419
  have eq1455 : ∀ X0 : G, (σ (σ X0)) = (M.op (σ (σ (M.op X0 X0))) (σ (σ X0))) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | exact superpose eq1393 eq1444
    | (have j0 := eq1444 X0
       have j1 := eq1393 X0 x
       grind)
    | exact resolve eq1444 eq1393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393 eq1444
  have eq1459 : ∀ X0 : G, (σ (σ X0)) = (M.op (σ (σ (M.op X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq1455 X0
       have j1 := eq1437 X0
       grind)
    | (have r₁ := eq1455 X0
       have r₂ := eq1437 X0
       grind)
    | exact resolve eq1455 eq1437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1437 eq1455
  have eq1543 : ∀ X0 : G, (τ (τ X0)) = (M.op (τ (τ (M.op X0 X0))) (τ (τ X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq705 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq705
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq705 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1563 : ∀ X0 : G, (τ (τ X0)) = (M.op (τ (τ (k (M.op X0 X0) (M.op X0 X0)))) (τ (τ X0))) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq705 (M.op X0 X0)
       have i₂ := eq1134 X0
       grind)
    | exact superpose eq1134 eq705
    | (have j1 := eq1134 X0
       grind)
    | exact resolve eq705 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq1577 : ∀ X0 : G, (τ (τ X0)) = (M.op (τ (τ (M.op X0 X0))) (τ (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1543 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543
  have eq1580 : ∀ X0 : G, (τ (τ X0)) = (M.op (τ (τ (k X0 (M.op X0 X0)))) (τ (τ X0))) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | exact superpose eq1285 eq1563
    | (have j0 := eq1563 X0
       have j1 := eq1285 X0 x
       grind)
    | exact resolve eq1563 eq1285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285 eq1563
  have eq1596 : ∀ X0 : G, (τ (τ X0)) = (M.op (τ (τ (M.op X0 X0))) (τ (τ X0))) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | exact superpose eq1294 eq1580
    | (have j0 := eq1580 X0
       have j1 := eq1294 X0 x
       grind)
    | exact resolve eq1580 eq1294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294 eq1580
  have eq1603 : ∀ X0 : G, (τ (τ X0)) = (M.op (τ (τ (M.op X0 X0))) (τ (τ X0))) := by
    intro X0
    first
    | (have j0 := eq1596 X0
       have j1 := eq1577 X0
       grind)
    | (have r₁ := eq1596 X0
       have r₂ := eq1577 X0
       grind)
    | exact resolve eq1596 eq1577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1577 eq1596
  have eq2079 : ∀ X0 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq1290 (M.op X0 X0)
       have i₂ := eq1209 X0
       grind)
    | exact superpose eq1209 eq1290
    | (have j0 := eq1290 X0
       have j1 := eq1209 (σ X0)
       grind)
    | exact resolve eq1290 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290
  have eq2090 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have j0 := eq2079 X0
       have j1 := eq1328 X0
       grind)
    | (have r₁ := eq2079 X0
       have r₂ := eq1328 X0
       grind)
    | (have r₁ := eq2079 (σ X0)
       have r₂ := eq1328 X0
       grind)
    | exact resolve eq2079 eq1328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2079
  have eq2320 : ∀ X0 : G, (σ X0) = (M.op (σ (σ (M.op (τ X0) (τ X0)))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1459 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1459
    | exact resolve eq1459 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1459
  have eq2371 : ∀ X0 : G, (τ X0) = (M.op (τ (τ (M.op (σ X0) (σ X0)))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1603 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1603
    | exact resolve eq1603 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1603
  have eq2450 : ∀ X0 : G, (σ X0) = (M.op (σ (σ (τ X0))) (σ X0)) ∨ (τ X0) ≠ (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2320 X0
       have i₂ := eq1209 (τ X0)
       grind)
    | exact superpose eq1209 eq2320
    | (have j1 := eq1209 (τ X0)
       grind)
    | exact resolve eq2320 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2320
  have eq2482 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ X0) ≠ (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2450 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2450
    | (have j0 := eq2450 X0
       grind)
    | exact resolve eq2450 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2450
  have eq2508 : ∀ X0 : G, (τ X0) = (M.op (τ (τ (σ X0))) (τ X0)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2371 X0
       have i₂ := eq1134 (σ X0)
       grind)
    | exact superpose eq1134 eq2371
    | (have j1 := eq1134 (σ X0)
       grind)
    | exact resolve eq2371 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134 eq2371
  have eq2542 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2508 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2508
    | (have j0 := eq2508 X0
       grind)
    | exact resolve eq2508 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2508
  have eq2759 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X0) ≠ X0 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq970 X0 X1
       have i₂ := eq1005 X0 X1
       grind)
    | exact superpose eq1005 eq970
    | (have j0 := eq970 X0 X1
       have j1 := eq1005 X0 X1
       grind)
    | exact resolve eq970 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2783 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (M.op X0 (M.op (M.op X1 X0) X1)) ∨ (M.op (M.op X1 X0) X1) ≠ (k (M.op (M.op X1 X0) X1) (M.op (M.op X1 X0) X1)) ∨ (k X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1005 (M.op (M.op X1 X0) X1) X0
       have i₂ := eq970 X1 X0
       grind)
    | exact superpose eq970 eq1005
    | (have j0 := eq1005 (M.op (M.op X1 X0) X1) X1
       have j1 := eq970 (M.op (M.op X1 X0) X1) X1
       grind)
    | exact resolve eq1005 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq2786 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq2759 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2759
  have eq2790 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op (M.op X1 X0) X1) ≠ (k (M.op (M.op X1 X0) X1) (M.op (M.op X1 X0) X1)) ∨ (k X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | exact superpose eq1005 eq2783
    | (have j0 := eq2783 X0 X1
       have j1 := eq1005 (M.op (M.op X1 X0) X1) X1
       grind)
    | exact resolve eq2783 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2783
  have eq2835 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X1 X1) ≠ X1 ∨ (k X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | exact superpose eq1005 eq2790
    | (have j0 := eq2790 X0 X1
       have j1 := eq1005 X1 X1
       grind)
    | exact resolve eq2790 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005 eq2790
  have eq2836 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have j0 := eq2835 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2835
  have eq3069 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ X0)) ∨ (M.op X0 X0) ≠ X0 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq68 X1 X0
       have i₂ := eq2836 (τ X1) X0
       grind)
    | exact superpose eq2836 eq68
    | (have j0 := eq68 X0 X0
       have j1 := eq2836 X0 X0
       grind)
    | (have r₁ := eq68 X0 X1
       have r₂ := eq2836 X1 X1
       grind)
    | exact resolve eq68 eq2836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq2836
  have eq3092 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ X0)) ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq3069 X0 X1
       have j1 := eq2786 X0 X1
       grind)
    | (have r₁ := eq3069 X0 (σ X0)
       have r₂ := eq2786 (σ X0) X1
       grind)
    | (have r₁ := eq3069 X1 X1
       have r₂ := eq2786 X1 X1
       grind)
    | exact resolve eq3069 eq2786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3069
  have eq3356 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ X0)) ∨ (M.op X0 X0) ≠ (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3092 (M.op X0 X0) X1
       have i₂ := eq1209 X0
       grind)
    | exact superpose eq1209 eq3092
    | (have j0 := eq3092 X0 X1
       have j1 := eq1209 X0
       grind)
    | exact resolve eq3092 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3381 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq3092 X0 X1
       grind)
    | exact superpose eq3092 eq12
    | (have j0 := eq12 X0 (σ X0)
       have j1 := eq3092 X0 X1
       grind)
    | exact resolve eq12 eq3092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3092
  have eq3405 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq3381 X0 X1
       have j1 := eq972 X0
       grind)
    | (have r₁ := eq3381 X0 X1
       have r₂ := eq972 X0
       grind)
    | exact resolve eq3381 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972 eq3381
  have eq3415 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ X0)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq3356 X0 X1
       have j1 := eq2090 X0
       grind)
    | (have r₁ := eq3356 X0 X1
       have r₂ := eq2090 X0
       grind)
    | exact resolve eq3356 eq2090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3356
  have eq3737 : ∀ X0 X3 : G, (M.op (σ X0) X3) = X3 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X3
    first
    | (have i₁ := eq63 (σ X0) x x X3
       have i₂ := eq3405 X0 (M.op (M.op (M.op x (σ X0)) (M.op x x)) X3)
       grind)
    | exact superpose eq3405 eq63
    | (have j1 := eq3405 X0 x
       grind)
    | exact resolve eq63 eq3405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3405
  have eq3791 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (M.op X0 X0) ≠ (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3737 (M.op X0 X0) X1
       have i₂ := eq1209 X0
       grind)
    | exact superpose eq1209 eq3737
    | (have j0 := eq3737 X0 X1
       have j1 := eq1209 X0
       grind)
    | (have r₁ := eq3737 X0 (σ X0)
       have r₂ := eq1209 (σ X0)
       grind)
    | exact resolve eq3737 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq3802 : (σ (M.op x y)) ≠ (σ y) ∨ x ≠ (k x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3737 x (σ y)
       grind)
    | exact superpose eq3737 eq16
    | (have j1 := eq3737 x x
       grind)
    | exact resolve eq16 eq3737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3737
  have eq3855 : (σ y) ≠ (σ y) ∨ x ≠ (k x x) := by
    first
    | exact superpose eq2786 eq3802
    | (have j1 := eq2786 x x
       grind)
    | exact resolve eq3802 eq2786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2786 eq3802
  have eq3856 : x ≠ (k x x) := by grind
  clear eq3855
  have eq3859 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq3791 X0 X1
       have j1 := eq2090 X0
       grind)
    | (have r₁ := eq3791 X0 (σ X0)
       have r₂ := eq2090 (σ X0)
       grind)
    | (have r₁ := eq3791 X0 X1
       have r₂ := eq2090 X0
       grind)
    | exact resolve eq3791 eq2090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2090 eq3791
  have eq3870 : x ≠ (M.op x x) ∨ x ≠ (M.op x x) := by
    first
    | (have i₁ := eq3856
       have i₂ := eq12 x x
       grind)
    | exact superpose eq12 eq3856
    | (have j1 := eq12 x x
       grind)
    | exact resolve eq3856 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3856
  have eq3871 : x ≠ (M.op x x) := by grind
  clear eq3870
  have eq3881 : ∀ X0 X1 : G, (τ X0) ≠ (M.op (τ X0) (τ X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3859 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3859
    | (have j0 := eq3859 (τ X0) X1
       grind)
    | exact resolve eq3859 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3913 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ X1) X2) X0) X2) = X2 ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X1) X0
       have i₂ := eq3859 X1 X0
       grind)
    | exact superpose eq3859 eq9
    | (have j1 := eq3859 X1 X1
       grind)
    | exact resolve eq9 eq3859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3952 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X2) = X2 ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq3859 eq3913
    | (have j0 := eq3913 X0 X1 X2
       have j1 := eq3859 X1 X1
       grind)
    | (have r₁ := eq3913 X0 (σ X0) X2
       have r₂ := eq3859 X0 (σ X0)
       grind)
    | exact resolve eq3913 eq3859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3859 eq3913
  have eq4166 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (τ (σ X0))) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 (σ X0)
       have i₂ := eq3415 X0 (σ X1)
       grind)
    | exact superpose eq3415 eq29
    | (have j1 := eq3415 X0 X1
       grind)
    | exact resolve eq29 eq3415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3415
  have eq4180 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4166 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4166
    | (have j0 := eq4166 X0 X1
       grind)
    | exact resolve eq4166 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4166
  have eq4240 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq4180 X0 X1
       grind)
    | exact superpose eq4180 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq4180 X0 X1
       grind)
    | exact resolve eq12 eq4180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4180
  have eq4272 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq4240 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4240
  have eq4343 : ∀ X0 X3 : G, (M.op X0 X3) = X3 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X3
    first
    | (have i₁ := eq63 X0 x x X3
       have i₂ := eq4272 X0 (M.op (M.op (M.op x X0) (M.op x x)) X3)
       grind)
    | exact superpose eq4272 eq63
    | (have j1 := eq4272 X3 X0
       grind)
    | exact resolve eq63 eq4272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq4272
  have eq4499 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4343 (σ x) (σ y)
       grind)
    | exact superpose eq4343 eq16
    | (have j1 := eq4343 (σ x) x
       grind)
    | exact resolve eq16 eq4343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4343
  have eq5748 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq621 (τ X0)
       grind)
    | exact superpose eq621 eq19
    | (have j1 := eq621 (τ X0)
       grind)
    | exact resolve eq19 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq5817 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5748 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq5748
    | (have j0 := eq5748 X0
       grind)
    | exact resolve eq5748 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5748
  have eq5839 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5817 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5817
    | (have j0 := eq5817 X0
       grind)
    | exact resolve eq5817 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5817
  have eq5856 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5839 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5839
    | (have j0 := eq5839 X0
       grind)
    | exact resolve eq5839 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5839
  have eq5970 : ∀ X0 X1 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3952 X0 X1 (k X0 X0)
       have i₂ := eq654 X0
       grind)
    | exact superpose eq654 eq3952
    | (have j0 := eq3952 X0 X1 x
       grind)
    | exact resolve eq3952 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654 eq3952
  have eq7908 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 (k X0 X0) X0
       have i₂ := eq5856 X0
       grind)
    | exact superpose eq5856 eq14
    | (have j0 := eq14 X0 X0
       have j1 := eq5856 X0
       grind)
    | exact resolve eq14 eq5856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7921 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq5856 (τ X0)
       grind)
    | exact superpose eq5856 eq19
    | (have j1 := eq5856 (τ X0)
       grind)
    | exact resolve eq19 eq5856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5856
  have eq7924 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7908 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7908
  have eq7929 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq7921 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq7921
    | (have j0 := eq7921 X0
       grind)
    | exact resolve eq7921 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7921
  have eq7935 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7924 X0
       have j1 := eq5970 X0 x
       grind)
    | (have r₁ := eq7924 x
       have r₂ := eq5970 X0 x
       grind)
    | exact resolve eq7924 eq5970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5970 eq7924
  have eq7947 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq7929 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7929
    | (have j0 := eq7929 X0
       grind)
    | exact resolve eq7929 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7929
  have eq32054 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq79 X0 (k (τ X0) (τ X0))
       have i₂ := eq7935 (τ X0)
       grind)
    | exact superpose eq7935 eq79
    | (have j0 := eq79 X0 (k (τ X0) (τ X0))
       have j1 := eq7935 (τ X0)
       grind)
    | exact resolve eq79 eq7935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq7935
  have eq32072 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq32054 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32054
  have eq32101 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq32072 X0
       have j1 := eq12 (τ X0) (τ X0)
       grind)
    | (have r₁ := eq32072 X0
       have r₂ := eq12 X0 (τ X0)
       grind)
    | exact resolve eq32072 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32072
  have eq32120 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq32101 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq32101
    | (have j0 := eq32101 X0
       grind)
    | exact resolve eq32101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq32101
  have eq32132 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq32120 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32120
    | (have j0 := eq32120 X0
       grind)
    | exact resolve eq32120 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32120
  have eq32141 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq32132 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq32132
    | (have j0 := eq32132 X0
       grind)
    | exact resolve eq32132 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq32132
  have eq32147 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | exact superpose eq7947 eq32141
    | (have j0 := eq32141 X0
       have j1 := eq7947 X0
       grind)
    | exact resolve eq32141 eq7947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7947 eq32141
  have eq33801 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (τ (σ X0)) = (τ (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq32147 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq32147
    | exact resolve eq32147 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32147
  have eq33894 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (τ (σ X0)) = (τ (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq33801 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq33801
    | (have j0 := eq33801 X0
       grind)
    | exact resolve eq33801 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33801
  have eq33913 : ∀ X0 : G, (τ (σ X0)) = (k X0 X0) ∨ (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq33894 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq33894
    | (have j0 := eq33894 X0
       grind)
    | exact resolve eq33894 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33894
  have eq33931 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq33913 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33913
    | (have j0 := eq33913 X0
       grind)
    | exact resolve eq33913 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33913
  have eq33948 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq33931 X0
       have j1 := eq1231 X0 X0
       grind)
    | (have r₁ := eq33931 X0
       have r₂ := eq1231 X0 x
       grind)
    | exact resolve eq33931 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231 eq33931
  have eq34036 : ∀ X0 : G, (k (k X0 X0) X0) = (τ (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k (k X0 X0) X0)
       have i₂ := eq33948 X0
       grind)
    | exact superpose eq33948 eq10
    | exact resolve eq10 eq33948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33948
  have eq34151 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq34036 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq34036
    | exact resolve eq34036 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34036
  have eq34325 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq34151 x
       have i₂ := eq12 x x
       grind)
    | exact superpose eq12 eq34151
    | (have j1 := eq12 X0 X0
       grind)
    | exact resolve eq34151 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34151
  have eq34436 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  clear eq34325
  have eq38180 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq588
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq588
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq588 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38184 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq38180
  have eq38185 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq1328 x
       grind)
    | (have r₁ := eq38184
       have r₂ := eq1328 (σ x)
       grind)
    | (have r₁ := eq38184
       have r₂ := eq1328 x
       grind)
    | exact resolve eq38184 eq1328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328 eq38184
  have eq46260 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (τ x) ≠ (M.op (τ x) (τ x)) := by
    first
    | (have i₁ := eq4499
       have i₂ := eq2482 x
       grind)
    | exact superpose eq2482 eq4499
    | (have j1 := eq2482 x
       grind)
    | (have r₁ := eq4499
       have r₂ := eq2482 x
       grind)
    | exact resolve eq4499 eq2482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2482 eq4499
  have eq46412 : (σ (M.op x y)) ≠ (σ y) ∨ (τ x) ≠ (M.op (τ x) (τ x)) := by grind
  clear eq46260
  have eq46453 : (σ y) ≠ (σ y) ∨ (τ x) ≠ (M.op (τ x) (τ x)) := by
    first
    | exact superpose eq3881 eq46412
    | (have j1 := eq3881 x x
       grind)
    | (have r₁ := eq46412
       have r₂ := eq3881 (τ x) (τ x)
       grind)
    | exact resolve eq46412 eq3881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3881 eq46412
  have eq46454 : (τ x) ≠ (M.op (τ x) (τ x)) := by grind
  clear eq46453
  have eq47708 : (τ x) ≠ (τ x) ∨ (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq46454
       have i₂ := eq2542 x
       grind)
    | exact superpose eq2542 eq46454
    | (have j1 := eq2542 x
       grind)
    | (have r₁ := eq46454
       have r₂ := eq2542 x
       grind)
    | exact resolve eq46454 eq2542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2542 eq46454
  have eq47861 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
  clear eq47708
  have eq178541 : (τ (σ y)) = (k x (τ (σ x))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq83 (σ x) x
       have i₂ := eq38185
       grind)
    | exact superpose eq38185 eq83
    | (have j0 := eq83 (σ x) x
       grind)
    | exact resolve eq83 eq38185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq178750 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq38185
  have eq178751 : (τ (σ y)) = (k x (τ (σ x))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq178541
  have eq178754 : y = (M.op x x) ∨ (σ x) ≠ (σ y) := by
    first
    | (have r₁ := eq178750
       have r₂ := eq47861
       grind)
    | exact resolve eq178750 eq47861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178750
  have eq178947 : (τ (σ y)) = (k x (τ (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq178751
       have r₂ := eq47861
       grind)
    | exact resolve eq178751 eq47861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178751
  have eq179080 : (τ (σ y)) = (k x (τ (σ x))) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq178947
       have r₂ := eq178754
       grind)
    | exact resolve eq178947 eq178754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178754 eq178947
  have eq179151 : (k x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq179080
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq179080
    | exact resolve eq179080 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179080
  have eq179166 : y = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq179151
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq179151
    | exact resolve eq179151 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179151
  have eq180528 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq179166
       grind)
    | exact superpose eq179166 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq179166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179166
  have eq180552 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq180528
  have eq180560 : y = (M.op x x) := by
    first
    | (have r₁ := eq180552
       have r₂ := eq3871
       grind)
    | exact resolve eq180552 eq3871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3871 eq180552
  have eq181204 : y = (k y x) := by
    first
    | (have i₁ := eq34436 x
       have i₂ := eq180560
       grind)
    | exact superpose eq180560 eq34436
    | exact resolve eq34436 eq180560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34436
  have eq181271 : y = (M.op x y) := by
    first
    | (have i₁ := eq109 x x
       have i₂ := eq180560
       grind)
    | exact superpose eq180560 eq109
    | exact resolve eq109 eq180560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180560
  have eq181339 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq181271
       grind)
    | exact superpose eq181271 eq16
    | exact resolve eq16 eq181271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181341 : (σ y) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq588
       have i₂ := eq181271
       grind)
    | exact superpose eq181271 eq588
    | exact resolve eq588 eq181271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588 eq181271
  have eq181360 : (σ y) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq181341
       have r₂ := eq47861
       grind)
    | exact resolve eq181341 eq47861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47861 eq181341
  have eq181363 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq181360
       have i₂ := eq181204
       grind)
    | exact superpose eq181204 eq181360
    | exact resolve eq181360 eq181204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181204 eq181360
  have eq181364 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq181363
  have eq181855 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq109 (σ x) (σ x)
       have i₂ := eq181364
       grind)
    | exact superpose eq181364 eq109
    | exact resolve eq109 eq181364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq181364
  have eq181938 : False := by grind
  exact eq181938

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_x_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq23 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq27 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | (have j0 := eq23 X0 X1
       grind)
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq34 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq37 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq12 (σ X0) X1
       grind)
    | exact superpose eq12 eq34
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq50
    | (have j0 := eq50 X0 X1
       grind)
    | exact resolve eq50 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq72 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq73 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (τ X0) ≠ (M.op (τ X0) (τ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27
    | (have j0 := eq27 X0 (τ X0)
       grind)
    | exact resolve eq27 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (M.op (σ X0) (σ X0)) (σ X0)) ∨ (M.op X0 X0) ≠ X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq27
  have eq90 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq97 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    grind
  have eq201 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq228 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq72 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq72
    | exact resolve eq72 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X1 : G, (k (M.op X1 X1) X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X1
    grind
  have eq232 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) ≠ X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq89 X0
       have i₂ := eq228 (σ X0)
       grind)
    | exact superpose eq228 eq89
    | (have j0 := eq89 X0
       grind)
    | exact resolve eq89 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq233 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq90 X0
       have i₂ := eq228 (σ X0)
       grind)
    | exact superpose eq228 eq90
    | (have j0 := eq90 X0
       grind)
    | exact resolve eq90 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq237 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq97 X0
       have i₂ := eq228 (τ X0)
       grind)
    | exact superpose eq228 eq97
    | (have j0 := eq97 X0
       grind)
    | exact resolve eq97 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq245 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have j0 := eq237 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq249 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have j0 := eq232 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq251 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq233 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq233
    | (have j0 := eq233 X0
       grind)
    | exact resolve eq233 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq252 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq72 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq228 (M.op X0 X1)
       grind)
    | exact superpose eq228 eq72
    | exact resolve eq72 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 X1 (M.op X0 X0) X0 X2
       have i₂ := eq228 X0
       grind)
    | exact superpose eq228 eq72
    | exact resolve eq72 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 X0 (M.op X0 X0) X1 X2
       have i₂ := eq228 X0
       grind)
    | exact superpose eq228 eq72
    | exact resolve eq72 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq255 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq228 X0
       grind)
    | exact superpose eq228 eq9
    | exact resolve eq9 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq228 X0
       grind)
    | exact superpose eq228 eq9
    | exact resolve eq9 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq255 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq255
    | exact resolve eq255 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 : G, (τ X0) ≠ (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq249 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq249
    | (have j0 := eq249 (τ X0)
       grind)
    | exact resolve eq249 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) (M.op (σ X0) X1)) (σ X0)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq256 (σ X0) X1
       have i₂ := eq249 X0
       grind)
    | exact superpose eq249 eq256
    | (have j1 := eq249 X0
       grind)
    | exact resolve eq256 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (σ X0)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq350 X0 X1
       have i₂ := eq268 (σ X0) X1
       grind)
    | exact superpose eq268 eq350
    | (have j0 := eq350 X0 X1
       grind)
    | exact resolve eq350 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq376 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op (σ X0) X1) (σ X0)) X2) X1) X2) = X2 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq73 X1 (σ X0) (σ X0) X2
       have i₂ := eq249 X0
       grind)
    | exact superpose eq249 eq73
    | (have j1 := eq249 X0
       grind)
    | exact resolve eq73 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq249
  have eq390 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ X0) X2) X1) X2) = X2 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq356 eq376
    | (have j0 := eq376 X0 X1 X2
       have j1 := eq356 X0 X1
       grind)
    | exact resolve eq376 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq392 : ∀ X0 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq245 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq245
    | (have j0 := eq245 (σ X0)
       grind)
    | exact resolve eq245 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq649 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq201 X0 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq201
    | (have j0 := eq201 X2 X2
       grind)
    | exact resolve eq201 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq650 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq201 x y
       grind)
    | exact superpose eq201 eq16
    | (have j1 := eq201 x y
       grind)
    | exact resolve eq16 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq667 : ∀ X0 : G, (σ X0) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq231 (σ x)
       have i₂ := eq201 x x
       grind)
    | exact superpose eq201 eq231
    | (have j0 := eq231 (σ X0)
       have j1 := eq201 X0 X0
       grind)
    | exact resolve eq231 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq670 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq228 (σ X0)
       have i₂ := eq201 X0 X0
       grind)
    | exact superpose eq201 eq228
    | (have j1 := eq201 X0 X0
       grind)
    | exact resolve eq228 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq672 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq201 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq673 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq672 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq675 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq670 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq678 : ∀ X0 : G, (σ X0) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq667 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq684 : ∀ X0 : G, (σ X0) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq678 X0
       have j1 := eq673 X0
       grind)
    | (have r₁ := eq678 X0
       have r₂ := eq673 X0
       grind)
    | exact resolve eq678 eq673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq687 : ∀ X0 : G, (σ X0) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq684 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq684
    | (have j0 := eq684 X0
       grind)
    | exact resolve eq684 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq757 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k (τ X0) (τ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq673 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq673
    | exact resolve eq673 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq761 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (M.op X0 X0) = X0 ∨ (σ X0) ≠ (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq392 X0
       have i₂ := eq673 X0
       grind)
    | exact superpose eq673 eq392
    | (have j0 := eq392 X0
       have j1 := eq673 X0
       grind)
    | (have r₁ := eq392 X0
       have r₂ := eq673 X0
       grind)
    | exact resolve eq392 eq673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq782 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq761 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq790 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq757 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq757
    | (have j0 := eq757 X0
       grind)
    | exact resolve eq757 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq791 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq790 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq790
    | (have j0 := eq790 X0
       grind)
    | exact resolve eq790 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq804 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = X0 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq256 X0 X1
       have i₂ := eq791 X0
       grind)
    | exact superpose eq791 eq256
    | (have j1 := eq791 X0
       grind)
    | exact resolve eq256 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq805 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = X1 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq255 X0 X1
       have i₂ := eq791 X0
       grind)
    | exact superpose eq791 eq255
    | (have j1 := eq791 X0
       grind)
    | exact resolve eq255 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq821 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (M.op X0 X0) = X0 ∨ (τ X0) ≠ (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq338 X0
       have i₂ := eq791 (τ X0)
       grind)
    | exact superpose eq791 eq338
    | (have j0 := eq338 X0
       have j1 := eq791 X0
       grind)
    | (have r₁ := eq338 X0
       have r₂ := eq791 (τ X0)
       grind)
    | exact resolve eq338 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq823 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k X1 X0) = X1 ∨ (τ X0) ≠ (k (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 X1
       have i₂ := eq791 (τ X0)
       grind)
    | exact superpose eq791 eq74
    | (have j0 := eq74 X0 X1
       have j1 := eq791 (τ X0)
       grind)
    | (have r₁ := eq74 X0 X1
       have r₂ := eq791 (τ X0)
       grind)
    | (have r₁ := eq74 X0 X0
       have r₂ := eq791 X0
       grind)
    | exact resolve eq74 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq791
  have eq824 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (τ X0) ≠ (k (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq823 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq826 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ X0) ≠ (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq821 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq833 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq824 X0 X1
       have i₂ := eq37 X0 X0
       grind)
    | exact superpose eq37 eq824
    | (have j0 := eq824 X0 X1
       grind)
    | exact resolve eq824 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq835 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq826 X0
       have i₂ := eq37 X0 X0
       grind)
    | exact superpose eq37 eq826
    | (have j0 := eq826 X0
       grind)
    | exact resolve eq826 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq844 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq804 X0 X1
       have i₂ := eq268 X0 X1
       grind)
    | exact superpose eq268 eq804
    | (have j0 := eq804 X0 X1
       grind)
    | exact resolve eq804 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq862 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq833 (σ X0) X1
       have i₂ := eq34 X0 (σ X0)
       grind)
    | exact superpose eq34 eq833
    | (have j0 := eq833 (σ X0) X1
       grind)
    | exact resolve eq833 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq833
  have eq873 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq862 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq862
    | (have j0 := eq862 X0 X1
       grind)
    | exact resolve eq862 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq892 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq873 X1 (σ X0)
       grind)
    | exact superpose eq873 eq15
    | (have j1 := eq873 X1 X1
       grind)
    | exact resolve eq15 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1058 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq835 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq835
    | (have j0 := eq835 X0
       have j1 := eq14 X0 X0
       grind)
    | exact resolve eq835 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq1084 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1058 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058
  have eq1122 : ∀ X0 : G, (τ (σ X0)) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k (k X0 X0) X0)
       have i₂ := eq687 X0
       grind)
    | exact superpose eq687 eq10
    | (have j1 := eq687 X0
       grind)
    | exact resolve eq10 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq1171 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1122 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1122
    | (have j0 := eq1122 X0
       grind)
    | exact resolve eq1122 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122
  have eq1323 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq782 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq782
    | (have j0 := eq782 X0
       have j1 := eq14 X0 X0
       grind)
    | exact resolve eq782 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq1349 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1323 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323
  have eq2062 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X0) ≠ X0 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq805 X0 X1
       have i₂ := eq844 X0 X1
       grind)
    | exact superpose eq844 eq805
    | (have j0 := eq805 X0 X1
       have j1 := eq844 X0 X1
       grind)
    | exact resolve eq805 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805 eq844
  have eq2078 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq2062 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2062
  have eq2146 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2078 (σ x) (σ y)
       grind)
    | exact superpose eq2078 eq16
    | (have j1 := eq2078 (σ x) x
       grind)
    | exact resolve eq16 eq2078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2176 : (σ x) ≠ (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq2146
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq2146
    | exact resolve eq2146 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2146
  have eq2453 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) ≠ (σ y) ∨ x ≠ (k x x) := by
    first
    | (have i₁ := eq2176
       have i₂ := eq892 x x
       grind)
    | exact superpose eq892 eq2176
    | (have j1 := eq892 x x
       grind)
    | (have r₁ := eq2176
       have r₂ := eq892 x x
       grind)
    | exact resolve eq2176 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892 eq2176
  have eq2454 : (σ (M.op x y)) ≠ (σ y) ∨ x ≠ (k x x) := by grind
  clear eq2453
  have eq2458 : (σ y) ≠ (σ y) ∨ x ≠ (k x x) := by
    first
    | exact superpose eq2078 eq2454
    | (have j1 := eq2078 x x
       grind)
    | exact resolve eq2454 eq2078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2454
  have eq2459 : x ≠ (k x x) := by grind
  clear eq2458
  have eq2465 : x ≠ x ∨ x ≠ (M.op x x) := by
    first
    | (have i₁ := eq2459
       have i₂ := eq12 x x
       grind)
    | exact superpose eq12 eq2459
    | (have j1 := eq12 x x
       grind)
    | (have r₁ := eq2459
       have r₂ := eq12 x x
       grind)
    | exact resolve eq2459 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2459
  have eq2466 : x ≠ (M.op x x) := by grind
  clear eq2465
  have eq4971 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (σ X0) X2)) X1) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq253 (σ X0) X1 X2
       have i₂ := eq390 X0 X1 (σ X0)
       grind)
    | exact superpose eq390 eq253
    | (have j1 := eq390 X0 X1 X2
       grind)
    | exact resolve eq253 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq4972 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq255 (σ X0) X1
       have i₂ := eq390 X0 X1 (σ X0)
       grind)
    | exact superpose eq390 eq255
    | (have j1 := eq390 X0 X1 x
       grind)
    | exact resolve eq255 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq390
  have eq5016 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq4972 eq4971
    | (have j0 := eq4971 X0 X1 X2
       have j1 := eq4972 X0 X1
       grind)
    | (have r₁ := eq4971 (σ X0) X1 X2
       have r₂ := eq4972 X0 (σ X0)
       grind)
    | exact resolve eq4971 eq4972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4971
  have eq5020 : ∀ X0 X1 : G, (τ X0) ≠ (M.op (τ X0) (τ X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4972 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4972
    | (have j0 := eq4972 (τ X0) X1
       grind)
    | exact resolve eq4972 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5034 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq356 X1 X0
       have i₂ := eq4972 X1 X0
       grind)
    | exact superpose eq4972 eq356
    | (have j0 := eq356 X1 X1
       have j1 := eq4972 X1 X1
       grind)
    | (have r₁ := eq356 (σ X0) X1
       have r₂ := eq4972 X0 (σ X0)
       grind)
    | exact resolve eq356 eq4972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4972
  have eq5086 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have j0 := eq5034 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5034
  have eq5437 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5020 X0 X1
       have i₂ := eq245 X0
       grind)
    | exact superpose eq245 eq5020
    | (have j0 := eq5020 X0 X1
       have j1 := eq245 X0
       grind)
    | (have r₁ := eq5020 X0 X1
       have r₂ := eq245 X0
       grind)
    | (have r₁ := eq5020 X0 X0
       have r₂ := eq245 X0
       grind)
    | exact resolve eq5020 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq5440 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (M.op X0 X1) = X1 ∨ (τ X0) ≠ (k (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5020 X0 X1
       have i₂ := eq2078 (τ X0) (τ X0)
       grind)
    | exact superpose eq2078 eq5020
    | (have j0 := eq5020 X0 X1
       have j1 := eq2078 X0 X1
       grind)
    | (have r₁ := eq5020 X0 X1
       have r₂ := eq2078 (τ X0) (τ X0)
       grind)
    | exact resolve eq5020 eq2078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5020
  have eq5441 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (τ X0) ≠ (k (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq5440 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5440
  have eq5444 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq5437 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5437
  have eq5446 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5441 X0 X1
       have i₂ := eq37 X0 X0
       grind)
    | exact superpose eq37 eq5441
    | (have j0 := eq5441 X0 X1
       grind)
    | exact resolve eq5441 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5441
  have eq5488 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X2) X0) = X0 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq254 X0 X1 X2
       have i₂ := eq5444 X0 (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X2)
       grind)
    | exact superpose eq5444 eq254
    | (have j1 := eq5444 (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X2) X0
       grind)
    | exact resolve eq254 eq5444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq5542 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5444 (σ x) (σ y)
       grind)
    | exact superpose eq5444 eq16
    | (have j1 := eq5444 (σ x) x
       grind)
    | exact resolve eq16 eq5444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5587 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X2) X0) = X0 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq5444 eq5488
    | (have j0 := eq5488 X0 X1 X2
       have j1 := eq5444 (M.op (M.op (M.op X0 X0) X1) X2) X0
       grind)
    | (have r₁ := eq5488 X1 X1 X2
       have r₂ := eq5444 X1 X1
       grind)
    | exact resolve eq5488 eq5444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5488
  have eq5598 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) X0) = X0 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq5444 eq5587
    | (have j0 := eq5587 X0 X1 X2
       have j1 := eq5444 (M.op (M.op X0 X1) X2) X0
       grind)
    | (have r₁ := eq5587 X1 X1 X2
       have r₂ := eq5444 X1 X1
       grind)
    | exact resolve eq5587 eq5444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5587
  have eq5600 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = X0 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq5444 eq5598
    | (have j0 := eq5598 X0 X1 X2
       have j1 := eq5444 (M.op X1 X2) X0
       grind)
    | (have r₁ := eq5598 X1 X1 X2
       have r₂ := eq5444 X1 X1
       grind)
    | exact resolve eq5598 eq5444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5444 eq5598
  have eq5604 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5446 (σ X0) X1
       have i₂ := eq873 X0 (σ X0)
       grind)
    | exact superpose eq873 eq5446
    | (have j0 := eq5446 (σ X0) X1
       have j1 := eq873 X0 X1
       grind)
    | exact resolve eq5446 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq5614 : ∀ X0 X1 : G, (τ (τ X0)) ≠ (τ (τ X0)) ∨ (M.op (τ X0) X1) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5446 (τ X0) X1
       have i₂ := eq58 (τ X0) X0
       grind)
    | exact superpose eq58 eq5446
    | (have j0 := eq5446 (τ X0) X1
       have j1 := eq58 X0 X0
       grind)
    | (have r₁ := eq5446 X1 X1
       have r₂ := eq58 X0 X1
       grind)
    | exact resolve eq5446 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5446
  have eq5639 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq5614 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5614
  have eq5649 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq5604 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5604
  have eq5661 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5639 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5639
    | (have j0 := eq5639 (σ X0) X1
       grind)
    | exact resolve eq5639 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5836 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (M.op X1 X1) ≠ X1 ∨ (k X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq356 X1 X0
       have i₂ := eq5649 X1 X0
       grind)
    | exact superpose eq5649 eq356
    | (have j0 := eq356 X1 X1
       have j1 := eq5649 X1 X1
       grind)
    | (have r₁ := eq356 (σ X0) X1
       have r₂ := eq5649 X0 (σ X0)
       grind)
    | exact resolve eq356 eq5649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356 eq5649
  have eq5901 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (k X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have j0 := eq5836 X0 X1
       have j1 := eq2078 X0 (σ X1)
       grind)
    | (have r₁ := eq5836 X0 X1
       have r₂ := eq2078 X1 X1
       grind)
    | exact resolve eq5836 eq2078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2078 eq5836
  have eq6067 : ∀ X0 X2 : G, (M.op X0 X2) = X2 ∨ (M.op X2 X2) ≠ X2 := by
    intro X0 X2
    first
    | (have i₁ := eq5600 X2 (M.op X0 (M.op x X0)) X0
       have i₂ := eq252 x X0
       grind)
    | exact superpose eq252 eq5600
    | (have j0 := eq5600 X2 x X2
       grind)
    | exact resolve eq5600 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq5600
  have eq7001 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (τ X0) ≠ (k (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5901 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5901
    | (have j0 := eq5901 X0 (τ X0)
       grind)
    | exact resolve eq5901 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5901
  have eq7111 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7001 X0 X1
       have i₂ := eq37 X0 X0
       grind)
    | exact superpose eq37 eq7001
    | (have j0 := eq7001 X0 X1
       grind)
    | exact resolve eq7001 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7001
  have eq7126 : ∀ X0 X1 : G, (τ (τ X0)) ≠ (τ (τ X0)) ∨ (τ X0) = (M.op X1 (τ X0)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7111 (τ X0) X1
       have i₂ := eq58 (τ X0) X0
       grind)
    | exact superpose eq58 eq7111
    | (have j0 := eq7111 (τ X0) X1
       have j1 := eq58 X0 X0
       grind)
    | (have r₁ := eq7111 X1 X1
       have r₂ := eq58 X0 X1
       grind)
    | exact resolve eq7111 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq7111
  have eq7151 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (τ X0)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq7126 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7126
  have eq8024 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (M.op X0 X1) = X1 ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5661 X0 X1
       have i₂ := eq1171 X0
       grind)
    | exact superpose eq1171 eq5661
    | (have j0 := eq5661 X0 X1
       have j1 := eq1171 X0
       grind)
    | (have r₁ := eq5661 X0 X1
       have r₂ := eq1171 X0
       grind)
    | exact resolve eq5661 eq1171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171
  have eq8059 : ∀ X0 X1 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq8024 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8024
  have eq8135 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq8059 (τ X0) X1
       grind)
    | exact superpose eq8059 eq19
    | (have j1 := eq8059 (τ X0) X1
       grind)
    | exact resolve eq19 eq8059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8059
  have eq8148 : ∀ X0 X1 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) X0) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8135 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq8135
    | (have j0 := eq8135 X0 X1
       grind)
    | exact resolve eq8135 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8135
  have eq8182 : ∀ X0 X1 : G, (k (k X0 X0) X0) = X0 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8148 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8148
    | (have j0 := eq8148 X0 X1
       grind)
    | exact resolve eq8148 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8148
  have eq8562 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op (τ X0) X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8182 X0 X1
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq8182
    | (have j0 := eq8182 X0 X1
       have j1 := eq14 X0 X0
       grind)
    | exact resolve eq8182 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8632 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op (τ (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq8182 (τ X0) X1
       grind)
    | exact superpose eq8182 eq19
    | (have j1 := eq8182 (τ X0) X1
       grind)
    | exact resolve eq19 eq8182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8182
  have eq8642 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op (τ X0) X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq8562 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8562
  have eq8645 : ∀ X0 X1 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) X0) ∨ (M.op (τ (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8632 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq8632
    | (have j0 := eq8632 X0 X1
       grind)
    | exact resolve eq8632 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8632
  have eq8676 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq8642 X0 X1
       have j1 := eq5639 X0 X1
       grind)
    | (have r₁ := eq8642 X0 (τ X0)
       have r₂ := eq5639 (τ X0) X1
       grind)
    | (have r₁ := eq8642 X0 X1
       have r₂ := eq5639 X0 X1
       grind)
    | exact resolve eq8642 eq5639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5639 eq8642
  have eq8679 : ∀ X0 X1 : G, (k (k X0 X0) X0) = X0 ∨ (M.op (τ (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8645 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8645
    | (have j0 := eq8645 X0 X1
       grind)
    | exact resolve eq8645 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8645
  have eq9308 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) ∨ (M.op (τ (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq8676 (σ X0) X1
       grind)
    | exact superpose eq8676 eq26
    | (have j1 := eq8676 (σ X0) X1
       grind)
    | exact resolve eq26 eq8676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq8676
  have eq9340 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 ∨ (M.op (τ (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9308 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9308
    | (have j0 := eq9308 X0 X1
       grind)
    | exact resolve eq9308 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9308
  have eq9363 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9340 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9340
    | (have j0 := eq9340 X0 X1
       grind)
    | exact resolve eq9340 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9340
  have eq12679 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op (τ (τ (τ X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq8679 (τ X0) X1
       grind)
    | exact superpose eq8679 eq19
    | (have j1 := eq8679 (τ X0) X1
       grind)
    | exact resolve eq19 eq8679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8679
  have eq12692 : ∀ X0 X1 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) X0) ∨ (M.op (τ (τ (τ X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12679 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq12679
    | (have j0 := eq12679 X0 X1
       grind)
    | exact resolve eq12679 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12679
  have eq12726 : ∀ X0 X1 : G, (M.op (τ (τ (τ X0))) X1) = X1 ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12692 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12692
    | (have j0 := eq12692 X0 X1
       grind)
    | exact resolve eq12692 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12692
  have eq19990 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq650
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq650
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq650 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19993 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq19990
  have eq19995 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq392 x
       grind)
    | (have r₁ := eq19993
       have r₂ := eq392 x
       grind)
    | exact resolve eq19993 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392 eq19993
  have eq19997 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq19995
       have r₂ := eq2466
       grind)
    | exact resolve eq19995 eq2466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19995
  have eq20002 : (σ y) = (σ (k x x)) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq19997
       have i₂ := eq201 x x
       grind)
    | exact superpose eq201 eq19997
    | (have j1 := eq201 x x
       grind)
    | exact resolve eq19997 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq20016 : (σ x) ≠ (σ y) ∨ (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5542
       have i₂ := eq19997
       grind)
    | exact superpose eq19997 eq5542
    | exact resolve eq5542 eq19997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5542
  have eq20027 : ∀ X0 : G, y = (M.op x x) ∨ (M.op x X0) = X0 ∨ (σ x) ≠ (σ y) := by
    intro X0
    first
    | (have i₁ := eq5661 x X0
       have i₂ := eq19997
       grind)
    | exact superpose eq19997 eq5661
    | (have j0 := eq5661 x X0
       grind)
    | exact resolve eq5661 eq19997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20052 : (τ (σ x)) ≠ (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1084 (σ x)
       have i₂ := eq19997
       grind)
    | exact superpose eq19997 eq1084
    | exact resolve eq1084 eq19997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq20082 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq268 (σ x) (σ x)
       have i₂ := eq19997
       grind)
    | exact superpose eq19997 eq268
    | exact resolve eq268 eq19997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20119 : (σ y) = (σ (k x x)) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq20002
  have eq20132 : y ≠ (τ (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq20052
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq20052
    | exact resolve eq20052 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20052
  have eq20138 : (σ x) ≠ (σ y) ∨ (σ y) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20027 eq20016
    | exact resolve eq20016 eq20027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20016 eq20027
  have eq20139 : y = (M.op x x) ∨ (σ x) ≠ (σ y) := by grind
  clear eq20138
  have eq20156 : x ≠ y ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq20132
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq20132
    | exact resolve eq20132 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20132
  have eq20163 : y = (M.op x x) ∨ x ≠ y := by
    first
    | (have r₁ := eq20156
       have r₂ := eq20139
       grind)
    | exact resolve eq20156 eq20139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20156
  have eq20175 : x ≠ y ∨ x ≠ y := by
    first
    | (have i₁ := eq2466
       have i₂ := eq20163
       grind)
    | exact superpose eq20163 eq2466
    | exact resolve eq2466 eq20163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20163
  have eq20259 : x ≠ y := by grind
  clear eq20175
  have eq20399 : (σ x) ≠ (σ y) ∨ x = y ∨ (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq1349 x
       have i₂ := eq20139
       grind)
    | exact superpose eq20139 eq1349
    | exact resolve eq1349 eq20139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1349 eq20139
  have eq20465 : (σ x) ≠ (σ y) ∨ x = y := by grind
  clear eq20399
  have eq20471 : (σ x) ≠ (σ y) := by
    first
    | (have r₁ := eq20465
       have r₂ := eq20259
       grind)
    | exact resolve eq20465 eq20259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20465
  have eq21584 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20082
       grind)
    | exact superpose eq20082 eq16
    | exact resolve eq16 eq20082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20082
  have eq29121 : ∀ X0 : G, x = (k (τ (σ y)) x) ∨ (M.op x X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9363 x X0
       have i₂ := eq19997
       grind)
    | exact superpose eq19997 eq9363
    | (have j0 := eq9363 x X0
       grind)
    | exact resolve eq9363 eq19997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9363
  have eq29243 : ∀ X0 : G, y = (M.op x x) ∨ (M.op x X0) = X0 ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq29121 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq29121
    | (have j0 := eq29121 X0
       grind)
    | exact resolve eq29121 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29121
  have eq30586 : ∀ X0 : G, x = (k y x) ∨ x = y ∨ (M.op x X0) = X0 ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq231 x
       have i₂ := eq29243 X0
       grind)
    | exact superpose eq29243 eq231
    | (have j1 := eq29243 X0
       grind)
    | exact resolve eq231 eq29243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231 eq29243
  have eq30668 : ∀ X0 : G, x = (k y x) ∨ x = y ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq30586 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30586
  have eq30673 : ∀ X0 : G, x = (k y x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq30668 X0
       grind)
    | (have r₁ := eq30668 X0
       have r₂ := eq20259
       grind)
    | exact resolve eq30668 eq20259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30668
  have eq30685 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 y x
       have i₂ := eq30673 X0
       grind)
    | exact superpose eq30673 eq14
    | (have j0 := eq14 y x
       have j1 := eq30673 x
       grind)
    | exact resolve eq14 eq30673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30700 : ∀ X0 : G, y = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq30685 X0
       grind)
    | (have r₁ := eq30685 X0
       have r₂ := eq2466
       grind)
    | (have r₁ := eq30685 x
       have r₂ := eq2466
       grind)
    | exact resolve eq30685 eq2466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2466 eq30685
  have eq31108 : x = (k (τ (σ y)) x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq251 x
       have i₂ := eq19997
       grind)
    | exact superpose eq19997 eq251
    | exact resolve eq251 eq19997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq19997
  have eq31255 : x = (k (τ (σ y)) x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq31108
       have r₂ := eq20471
       grind)
    | exact resolve eq31108 eq20471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20471 eq31108
  have eq31294 : x = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq31255
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq31255
    | exact resolve eq31255 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31255
  have eq31302 : x = (k y x) ∨ x = y := by
    first
    | exact superpose eq30673 eq31294
    | exact resolve eq31294 eq30673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30673 eq31294
  have eq31304 : x = (k y x) := by
    first
    | (have r₁ := eq31302
       have r₂ := eq20259
       grind)
    | exact resolve eq31302 eq20259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31302
  have eq31306 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq650
       have i₂ := eq31304
       grind)
    | exact superpose eq31304 eq650
    | exact resolve eq650 eq31304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650 eq31304
  have eq31575 : ∀ X0 : G, y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq268 x x
       have i₂ := eq30700 X0
       grind)
    | exact superpose eq30700 eq268
    | (have j1 := eq30700 y
       grind)
    | exact resolve eq268 eq30700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30700
  have eq31728 : y ≠ y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq31575 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31575
  have eq31729 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq31728
  have eq31735 : (σ y) ≠ (σ y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21584
       have i₂ := eq31729
       grind)
    | exact superpose eq31729 eq21584
    | exact resolve eq21584 eq31729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21584 eq31729
  have eq31791 : y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq31735
  have eq31808 : x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq228 x
       have i₂ := eq31791
       grind)
    | exact superpose eq31791 eq228
    | exact resolve eq228 eq31791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq33769 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq675 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq675
    | (have j0 := eq675 X0
       have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq675 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33809 : ∀ X0 : G, (σ (τ X0)) = (M.op (k (σ (τ X0)) X0) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq675 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq675
    | (have j0 := eq675 (τ X0)
       grind)
    | exact resolve eq675 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq675
  have eq33924 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq33769 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33769
  have eq33974 : ∀ X0 : G, (σ (τ X0)) = (M.op (k (σ (τ X0)) X0) (σ (τ X0))) := by
    intro X0
    first
    | (have j0 := eq33809 X0
       have j1 := eq6067 (k (σ (τ X0)) X0) (σ (τ X0))
       grind)
    | (have r₁ := eq33809 X0
       have r₂ := eq6067 X0 (σ (τ X0))
       grind)
    | exact resolve eq33809 eq6067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6067 eq33809
  have eq33993 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq33924 X0
       have j1 := eq5661 (σ (M.op X0 X0)) (σ X0)
       grind)
    | (have r₁ := eq33924 X0
       have r₂ := eq5661 X0 x
       grind)
    | (have r₁ := eq33924 (σ X0)
       have r₂ := eq5661 X0 x
       grind)
    | exact resolve eq33924 eq5661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5661 eq33924
  have eq34005 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq33974 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq33974
    | exact resolve eq33974 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33974
  have eq34008 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq33993 X0
       have j1 := eq5086 (σ (M.op X0 X0)) X0
       grind)
    | (have r₁ := eq33993 x
       have r₂ := eq5086 X0 x
       grind)
    | exact resolve eq33993 eq5086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5086 eq33993
  have eq34049 : ∀ X0 : G, (τ X0) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq34005 (τ X0)
       have i₂ := eq37 X0 X0
       grind)
    | exact superpose eq37 eq34005
    | exact resolve eq34005 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq34005
  have eq34183 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq34008 x
       have i₂ := eq31791
       grind)
    | exact superpose eq31791 eq34008
    | exact resolve eq34008 eq31791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31791 eq34008
  have eq34440 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34049 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq34049
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq34049 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34049
  have eq34548 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq34440 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34440
  have eq34577 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq34548 X0
       have j1 := eq7151 X0 (τ (M.op X0 X0))
       grind)
    | (have r₁ := eq34548 X0
       have r₂ := eq7151 X0 x
       grind)
    | exact resolve eq34548 eq7151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34548
  have eq34755 : (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq34577 (σ x)
       have i₂ := eq31306
       grind)
    | exact superpose eq31306 eq34577
    | exact resolve eq34577 eq31306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31306 eq34577
  have eq34855 : (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have j1 := eq7151 (σ x) (τ (σ y))
       grind)
    | (have r₁ := eq34755
       have r₂ := eq7151 (σ x) x
       grind)
    | exact resolve eq34755 eq7151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7151 eq34755
  have eq34886 : x = (M.op (τ (σ y)) x) ∨ (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq34855
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq34855
    | exact resolve eq34855 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34855
  have eq34889 : x = (M.op y x) ∨ (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq34886
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq34886
    | exact resolve eq34886 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34886
  have eq34891 : x = (M.op y x) ∨ (σ x) ≠ (σ x) := by
    first
    | exact superpose eq31808 eq34889
    | exact resolve eq34889 eq31808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31808 eq34889
  have eq34892 : x = (M.op y x) := by grind
  clear eq34891
  have eq34949 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq5016 X0 y x
       have i₂ := eq34892
       grind)
    | exact superpose eq34892 eq5016
    | (have j0 := eq5016 X0 x x
       grind)
    | exact resolve eq5016 eq34892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34892
  have eq44736 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) ≠ X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq5016 X0 (σ y) (σ x)
       have i₂ := eq34183
       grind)
    | exact superpose eq34183 eq5016
    | (have j0 := eq5016 X0 x x
       grind)
    | exact resolve eq5016 eq34183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5016 eq34183
  have eq44746 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) ≠ X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq34949 eq44736
    | (have j0 := eq44736 X0
       have j1 := eq34949 X0
       grind)
    | exact resolve eq44736 eq34949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44736
  have eq44756 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have j0 := eq44746 X0
       grind)
    | (have r₁ := eq44746 X0
       have r₂ := eq20259
       grind)
    | exact resolve eq44746 eq20259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20259 eq44746
  have eq44759 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq44756 X0
       grind)
    | exact superpose eq44756 eq16
    | (have j1 := eq44756 X0
       grind)
    | exact resolve eq16 eq44756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44756
  have eq44822 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | exact superpose eq34949 eq44759
    | (have j0 := eq44759 X0
       have j1 := eq34949 X0
       grind)
    | exact resolve eq44759 eq34949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34949 eq44759
  have eq44823 : ∀ X0 : G, (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have j0 := eq44822 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44822
  have eq44880 : ∀ X0 : G, (τ (τ (τ X0))) ≠ (τ (τ (τ X0))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq44823 (τ (τ (τ X0)))
       have i₂ := eq12726 X0 (τ (τ (τ X0)))
       grind)
    | exact superpose eq12726 eq44823
    | (have j1 := eq12726 X0 x
       grind)
    | (have r₁ := eq44823 (τ (τ (τ X0)))
       have r₂ := eq12726 X0 (τ (τ (τ X0)))
       grind)
    | exact resolve eq44823 eq12726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12726
  have eq44915 : ∀ X0 : G, (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq44880 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44880
  have eq45654 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k (σ (τ X0)) X0)) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq649 (τ X0) X0 (τ X0)
       have i₂ := eq44915 (τ X0)
       grind)
    | exact superpose eq44915 eq649
    | (have j0 := eq649 (τ X0) X0 (τ X0)
       grind)
    | exact resolve eq649 eq44915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649 eq44915
  have eq45734 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k (σ (τ X0)) X0)) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have j0 := eq45654 X0
       grind)
    | (have r₁ := eq45654 X0
       have r₂ := eq44823 (σ (τ X0))
       grind)
    | exact resolve eq45654 eq44823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45654
  have eq45755 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq45734 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq45734
    | (have j0 := eq45734 X0
       grind)
    | exact resolve eq45734 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45734
  have eq45767 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq45755 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq45755
    | (have j0 := eq45755 X0
       grind)
    | exact resolve eq45755 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45755
  have eq50311 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq268 X0 (k X0 X0)
       have i₂ := eq45767 X0
       grind)
    | exact superpose eq45767 eq268
    | (have j1 := eq45767 X0
       grind)
    | exact resolve eq268 eq45767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45767
  have eq50585 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq50311 X0
       grind)
    | (have r₁ := eq50311 X0
       have r₂ := eq44823 X0
       grind)
    | exact resolve eq50311 eq44823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50311
  have eq52001 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq20119
       have i₂ := eq50585 x
       grind)
    | exact superpose eq50585 eq20119
    | exact resolve eq20119 eq50585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20119
  have eq52015 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq52001
       have r₂ := eq44823 (σ x)
       grind)
    | exact resolve eq52001 eq44823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44823 eq52001
  have eq52501 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq50585 (σ X0)
       grind)
    | exact superpose eq50585 eq15
    | exact resolve eq15 eq50585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52554 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq52501 X0
       have i₂ := eq50585 X0
       grind)
    | exact superpose eq50585 eq52501
    | exact resolve eq52501 eq50585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50585 eq52501
  have eq55566 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq268 (σ X0) (σ X0)
       have i₂ := eq52554 X0
       grind)
    | exact superpose eq52554 eq268
    | exact resolve eq268 eq52554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52554
  have eq55734 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq52015
       grind)
    | exact superpose eq52015 eq10
    | exact resolve eq10 eq52015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52015
  have eq55790 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq55734
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq55734
    | exact resolve eq55734 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55734
  have eq55791 : y = (M.op x x) := by grind
  clear eq55790
  have eq55863 : y = (M.op x y) := by
    first
    | (have i₁ := eq268 x x
       have i₂ := eq55791
       grind)
    | exact superpose eq55791 eq268
    | exact resolve eq268 eq55791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq55892 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq55863
       grind)
    | exact superpose eq55863 eq16
    | exact resolve eq16 eq55863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55863
  have eq57944 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq55566 x
       have i₂ := eq55791
       grind)
    | exact superpose eq55791 eq55566
    | exact resolve eq55566 eq55791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55566 eq55791
  have eq57998 : False := by grind
  exact eq57998

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_x_y_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq23 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq27 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | (have j0 := eq23 X0 X1
       grind)
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq34 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq37 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq12 (σ X0) X1
       grind)
    | exact superpose eq12 eq34
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq50
    | (have j0 := eq50 X0 X1
       grind)
    | exact resolve eq50 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq72 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq73 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (τ X0) ≠ (M.op (τ X0) (τ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27
    | (have j0 := eq27 X0 (τ X0)
       grind)
    | exact resolve eq27 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) ≠ X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq27
  have eq90 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq26
  have eq91 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have j0 := eq89 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq95 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq90 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90
    | (have j0 := eq90 X0
       grind)
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq103 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    grind
  have eq104 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ X1))) ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (τ X1)
       have i₂ := eq58 (σ X0) X1
       grind)
    | exact superpose eq58 eq34
    | (have j1 := eq58 X0 X1
       grind)
    | exact resolve eq34 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have j0 := eq103 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq110 : ∀ X0 X1 : G, (k X0 (τ (τ X1))) = X0 ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq104
    | (have j0 := eq104 X0 X1
       grind)
    | exact resolve eq104 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq127 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq110 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq110
    | (have j0 := eq110 X0 (σ X0)
       grind)
    | exact resolve eq110 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq145 : ∀ X0 : G, (τ X0) ≠ (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq91 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq91
    | (have j0 := eq91 (τ X0)
       grind)
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) (M.op (σ X0) X1)) (σ X0)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq9
    | (have j1 := eq91 X0
       grind)
    | exact resolve eq9 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq107 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq107
    | (have j0 := eq107 (σ X0)
       grind)
    | exact resolve eq107 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq215 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq34
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq34 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq72 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq72
    | exact resolve eq72 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq285 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq72 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq280 (M.op X0 X1)
       grind)
    | exact superpose eq280 eq72
    | exact resolve eq72 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 X1 (M.op X0 X0) X0 X2
       have i₂ := eq280 X0
       grind)
    | exact superpose eq280 eq72
    | exact resolve eq72 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 X0 (M.op X0 X0) X1 X2
       have i₂ := eq280 X0
       grind)
    | exact superpose eq280 eq72
    | exact resolve eq72 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq288 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq280 X0
       grind)
    | exact superpose eq280 eq9
    | exact resolve eq9 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq280 X0
       grind)
    | exact superpose eq280 eq9
    | exact resolve eq9 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq305 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq288 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq288
    | exact resolve eq288 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq313 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (σ X0)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq149 X0 X1
       have i₂ := eq305 (σ X0) X1
       grind)
    | exact superpose eq305 eq149
    | (have j0 := eq149 X0 X1
       grind)
    | exact resolve eq149 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq330 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op (σ X0) X1) (σ X0)) X2) X1) X2) = X2 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq73 X1 (σ X0) (σ X0) X2
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq73
    | (have j1 := eq91 X0
       grind)
    | exact resolve eq73 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq91
  have eq344 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ X0) X2) X1) X2) = X2 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq313 eq330
    | (have j0 := eq330 X0 X1 X2
       have j1 := eq313 X0 X1
       grind)
    | exact resolve eq330 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq677 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq214 x y
       grind)
    | exact superpose eq214 eq16
    | (have j1 := eq214 x y
       grind)
    | exact resolve eq16 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq280 (σ X0)
       have i₂ := eq214 X0 X0
       grind)
    | exact superpose eq214 eq280
    | (have j1 := eq214 X0 X0
       grind)
    | exact resolve eq280 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697 : ∀ X0 : G, (σ X0) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq699 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq214 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq700 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq699 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq702 : ∀ X0 : G, (σ X0) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq697 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq703 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq696 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq711 : ∀ X0 : G, (σ X0) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq702 X0
       have j1 := eq700 X0
       grind)
    | (have r₁ := eq702 X0
       have r₂ := eq700 X0
       grind)
    | exact resolve eq702 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq714 : ∀ X0 : G, (σ X0) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq711 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq711
    | (have j0 := eq711 X0
       grind)
    | exact resolve eq711 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq715 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k (τ X0) (τ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq700 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq700
    | exact resolve eq700 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq720 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k X1 (τ X0)) = X1 ∨ (σ X0) ≠ (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq127 X0 X1
       have i₂ := eq700 X0
       grind)
    | exact superpose eq700 eq127
    | (have j0 := eq127 X0 X1
       have j1 := eq700 X0
       grind)
    | (have r₁ := eq127 X0 X1
       have r₂ := eq700 X0
       grind)
    | exact resolve eq127 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq721 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (M.op X0 X0) = X0 ∨ (σ X0) ≠ (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq155 X0
       have i₂ := eq700 X0
       grind)
    | exact superpose eq700 eq155
    | (have j0 := eq155 X0
       have j1 := eq700 X0
       grind)
    | (have r₁ := eq155 X0
       have r₂ := eq700 X0
       grind)
    | exact resolve eq155 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq738 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq721 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq739 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq720 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq748 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq715 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq715
    | (have j0 := eq715 X0
       grind)
    | exact resolve eq715 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq749 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq748 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq748
    | (have j0 := eq748 X0
       grind)
    | exact resolve eq748 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq762 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = X0 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq289 X0 X1
       have i₂ := eq749 X0
       grind)
    | exact superpose eq749 eq289
    | (have j1 := eq749 X0
       grind)
    | exact resolve eq289 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq763 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = X1 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq288 X0 X1
       have i₂ := eq749 X0
       grind)
    | exact superpose eq749 eq288
    | (have j1 := eq749 X0
       grind)
    | exact resolve eq288 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq780 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (M.op X0 X0) = X0 ∨ (τ X0) ≠ (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq145 X0
       have i₂ := eq749 (τ X0)
       grind)
    | exact superpose eq749 eq145
    | (have j0 := eq145 X0
       have j1 := eq749 X0
       grind)
    | (have r₁ := eq145 X0
       have r₂ := eq749 (τ X0)
       grind)
    | exact resolve eq145 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq781 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k X1 X0) = X1 ∨ (τ X0) ≠ (k (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 X1
       have i₂ := eq749 (τ X0)
       grind)
    | exact superpose eq749 eq74
    | (have j0 := eq74 X0 X1
       have j1 := eq749 (τ X0)
       grind)
    | (have r₁ := eq74 X0 X1
       have r₂ := eq749 (τ X0)
       grind)
    | (have r₁ := eq74 X0 X0
       have r₂ := eq749 X0
       grind)
    | exact resolve eq74 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq749
  have eq782 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (τ X0) ≠ (k (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq781 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq783 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ X0) ≠ (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq780 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq791 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq782 X0 X1
       have i₂ := eq37 X0 X0
       grind)
    | exact superpose eq37 eq782
    | (have j0 := eq782 X0 X1
       grind)
    | exact resolve eq782 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq792 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq783 X0
       have i₂ := eq37 X0 X0
       grind)
    | exact superpose eq37 eq783
    | (have j0 := eq783 X0
       grind)
    | exact resolve eq783 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783
  have eq802 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq762 X0 X1
       have i₂ := eq305 X0 X1
       grind)
    | exact superpose eq305 eq762
    | (have j0 := eq762 X0 X1
       grind)
    | exact resolve eq762 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq820 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq791 (σ X0) X1
       have i₂ := eq34 X0 (σ X0)
       grind)
    | exact superpose eq34 eq791
    | (have j0 := eq791 (σ X0) X1
       grind)
    | exact resolve eq791 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791
  have eq831 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq820 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq820
    | (have j0 := eq820 X0 X1
       grind)
    | exact resolve eq820 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820
  have eq850 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq831 X1 (σ X0)
       grind)
    | exact superpose eq831 eq15
    | (have j1 := eq831 X1 X1
       grind)
    | exact resolve eq15 eq831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq853 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (σ X1)
       have i₂ := eq831 X1 (σ X0)
       grind)
    | exact superpose eq831 eq34
    | (have j1 := eq831 X1 X1
       grind)
    | exact resolve eq34 eq831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq861 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq853 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq853
    | (have j0 := eq853 X0 X1
       grind)
    | exact resolve eq853 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq867 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq861 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq861
    | (have j0 := eq861 X0 X1
       grind)
    | exact resolve eq861 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861
  have eq888 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (k X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq867 (σ X0) X1
       grind)
    | exact superpose eq867 eq34
    | (have j1 := eq867 X0 X1
       grind)
    | exact resolve eq34 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq902 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq888 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq888
    | (have j0 := eq888 X0 X1
       grind)
    | exact resolve eq888 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq932 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ X1))) ∨ (k X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (τ X1)
       have i₂ := eq902 (σ X0) X1
       grind)
    | exact superpose eq902 eq34
    | (have j1 := eq902 X0 X1
       grind)
    | exact resolve eq34 eq902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902
  have eq939 : ∀ X0 X1 : G, (k X0 (τ (τ X1))) = X0 ∨ (k X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq932 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq932
    | (have j0 := eq932 X0 X1
       grind)
    | exact resolve eq932 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932
  have eq1016 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq792 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq792
    | (have j0 := eq792 X0
       have j1 := eq14 X0 X0
       grind)
    | exact resolve eq792 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq1042 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1016 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016
  have eq1079 : ∀ X0 : G, (σ X0) = (σ (M.op X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq714 X0
       have i₂ := eq14 (k X0 X0) X0
       grind)
    | exact superpose eq14 eq714
    | (have j0 := eq714 X0
       have j1 := eq14 X0 X0
       grind)
    | exact resolve eq714 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq1156 : ∀ X0 : G, (σ X0) = (σ (M.op X0 (k X0 X0))) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1079 X0
       have j1 := eq155 X0
       grind)
    | (have r₁ := eq1079 X0
       have r₂ := eq155 X0
       grind)
    | (have r₁ := eq1079 (σ X0)
       have r₂ := eq155 X0
       grind)
    | exact resolve eq1079 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079
  have eq1281 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq738 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq738
    | (have j0 := eq738 X0
       have j1 := eq14 X0 X0
       grind)
    | exact resolve eq738 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq1307 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1281 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281
  have eq1518 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (τ X1)))) ∨ (k X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (τ (τ X1))
       have i₂ := eq939 (σ X0) X1
       grind)
    | exact superpose eq939 eq34
    | (have j1 := eq939 X0 X1
       grind)
    | exact resolve eq34 eq939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq1531 : ∀ X0 X1 : G, (k X0 (τ (τ (τ X1)))) = X0 ∨ (k X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1518 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1518
    | (have j0 := eq1518 X0 X1
       grind)
    | exact resolve eq1518 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518
  have eq1957 : ∀ X0 X1 : G, (σ (τ (τ (τ X0)))) ≠ (σ (τ (τ (τ X0)))) ∨ (k X1 (τ (τ (τ (τ X0))))) = X1 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq739 (τ (τ (τ X0))) X1
       have i₂ := eq1531 (τ (τ (τ X0))) X0
       grind)
    | exact superpose eq1531 eq739
    | (have j0 := eq739 (τ (τ (τ X0))) X1
       have j1 := eq1531 X1 (τ X0)
       grind)
    | (have r₁ := eq739 X0 (τ X0)
       have r₂ := eq1531 X0 (τ X0)
       grind)
    | exact resolve eq739 eq1531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739 eq1531
  have eq1978 : ∀ X0 X1 : G, (k X1 (τ (τ (τ (τ X0))))) = X1 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq1957 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957
  have eq2020 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X0) ≠ X0 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq763 X0 X1
       have i₂ := eq802 X0 X1
       grind)
    | exact superpose eq802 eq763
    | (have j0 := eq763 X0 X1
       have j1 := eq802 X0 X1
       grind)
    | exact resolve eq763 eq802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763 eq802
  have eq2036 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq2020 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2020
  have eq2104 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2036 (σ x) (σ y)
       grind)
    | exact superpose eq2036 eq16
    | (have j1 := eq2036 (σ x) x
       grind)
    | exact resolve eq16 eq2036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2134 : (σ x) ≠ (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq2104
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq2104
    | exact resolve eq2104 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2104
  have eq2411 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) ≠ (σ y) ∨ x ≠ (k x x) := by
    first
    | (have i₁ := eq2134
       have i₂ := eq850 x x
       grind)
    | exact superpose eq850 eq2134
    | (have j1 := eq850 x x
       grind)
    | (have r₁ := eq2134
       have r₂ := eq850 x x
       grind)
    | exact resolve eq2134 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850 eq2134
  have eq2412 : (σ (M.op x y)) ≠ (σ y) ∨ x ≠ (k x x) := by grind
  clear eq2411
  have eq2416 : (σ y) ≠ (σ y) ∨ x ≠ (k x x) := by
    first
    | exact superpose eq2036 eq2412
    | (have j1 := eq2036 x x
       grind)
    | exact resolve eq2412 eq2036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2412
  have eq2417 : x ≠ (k x x) := by grind
  clear eq2416
  have eq2423 : x ≠ x ∨ x ≠ (M.op x x) := by
    first
    | (have i₁ := eq2417
       have i₂ := eq12 x x
       grind)
    | exact superpose eq12 eq2417
    | (have j1 := eq12 x x
       grind)
    | (have r₁ := eq2417
       have r₂ := eq12 x x
       grind)
    | exact resolve eq2417 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2417
  have eq2424 : x ≠ (M.op x x) := by grind
  clear eq2423
  have eq4930 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (σ X0) X2)) X1) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq286 (σ X0) X1 X2
       have i₂ := eq344 X0 X1 (σ X0)
       grind)
    | exact superpose eq344 eq286
    | (have j1 := eq344 X0 X1 X2
       grind)
    | exact resolve eq286 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq4931 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq288 (σ X0) X1
       have i₂ := eq344 X0 X1 (σ X0)
       grind)
    | exact superpose eq344 eq288
    | (have j1 := eq344 X0 X1 x
       grind)
    | exact resolve eq288 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288 eq344
  have eq4975 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq4931 eq4930
    | (have j0 := eq4930 X0 X1 X2
       have j1 := eq4931 X0 X1
       grind)
    | (have r₁ := eq4930 (σ X0) X1 X2
       have r₂ := eq4931 X0 (σ X0)
       grind)
    | exact resolve eq4930 eq4931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4930
  have eq4979 : ∀ X0 X1 : G, (τ X0) ≠ (M.op (τ X0) (τ X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4931 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4931
    | (have j0 := eq4931 (τ X0) X1
       grind)
    | exact resolve eq4931 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4993 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq313 X1 X0
       have i₂ := eq4931 X1 X0
       grind)
    | exact superpose eq4931 eq313
    | (have j0 := eq313 X1 X1
       have j1 := eq4931 X1 X1
       grind)
    | (have r₁ := eq313 (σ X0) X1
       have r₂ := eq4931 X0 (σ X0)
       grind)
    | exact resolve eq313 eq4931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4931
  have eq5045 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have j0 := eq4993 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4993
  have eq5249 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4979 X0 X1
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq4979
    | (have j0 := eq4979 X0 X1
       have j1 := eq107 X0
       grind)
    | (have r₁ := eq4979 X0 X1
       have r₂ := eq107 X0
       grind)
    | (have r₁ := eq4979 X0 X0
       have r₂ := eq107 X0
       grind)
    | exact resolve eq4979 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq5252 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (M.op X0 X1) = X1 ∨ (τ X0) ≠ (k (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4979 X0 X1
       have i₂ := eq2036 (τ X0) (τ X0)
       grind)
    | exact superpose eq2036 eq4979
    | (have j0 := eq4979 X0 X1
       have j1 := eq2036 X0 X1
       grind)
    | (have r₁ := eq4979 X0 X1
       have r₂ := eq2036 (τ X0) (τ X0)
       grind)
    | exact resolve eq4979 eq2036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4979
  have eq5253 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (τ X0) ≠ (k (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq5252 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5252
  have eq5256 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq5249 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5249
  have eq5258 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5253 X0 X1
       have i₂ := eq37 X0 X0
       grind)
    | exact superpose eq37 eq5253
    | (have j0 := eq5253 X0 X1
       grind)
    | exact resolve eq5253 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5253
  have eq5447 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X2) X0) = X0 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq287 X0 X1 X2
       have i₂ := eq5256 X0 (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X2)
       grind)
    | exact superpose eq5256 eq287
    | (have j1 := eq5256 (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X2) X0
       grind)
    | exact resolve eq287 eq5256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq5501 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5256 (σ x) (σ y)
       grind)
    | exact superpose eq5256 eq16
    | (have j1 := eq5256 (σ x) x
       grind)
    | exact resolve eq16 eq5256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5546 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X2) X0) = X0 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq5256 eq5447
    | (have j0 := eq5447 X0 X1 X2
       have j1 := eq5256 (M.op (M.op (M.op X0 X0) X1) X2) X0
       grind)
    | (have r₁ := eq5447 X1 X1 X2
       have r₂ := eq5256 X1 X1
       grind)
    | exact resolve eq5447 eq5256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5447
  have eq5557 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) X0) = X0 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq5256 eq5546
    | (have j0 := eq5546 X0 X1 X2
       have j1 := eq5256 (M.op (M.op X0 X1) X2) X0
       grind)
    | (have r₁ := eq5546 X1 X1 X2
       have r₂ := eq5256 X1 X1
       grind)
    | exact resolve eq5546 eq5256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5546
  have eq5559 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = X0 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq5256 eq5557
    | (have j0 := eq5557 X0 X1 X2
       have j1 := eq5256 (M.op X1 X2) X0
       grind)
    | (have r₁ := eq5557 X1 X1 X2
       have r₂ := eq5256 X1 X1
       grind)
    | exact resolve eq5557 eq5256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5557
  have eq5563 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5258 (σ X0) X1
       have i₂ := eq831 X0 (σ X0)
       grind)
    | exact superpose eq831 eq5258
    | (have j0 := eq5258 (σ X0) X1
       have j1 := eq831 X0 X1
       grind)
    | exact resolve eq5258 eq831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq5573 : ∀ X0 X1 : G, (τ (τ X0)) ≠ (τ (τ X0)) ∨ (M.op (τ X0) X1) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5258 (τ X0) X1
       have i₂ := eq58 (τ X0) X0
       grind)
    | exact superpose eq58 eq5258
    | (have j0 := eq5258 (τ X0) X1
       have j1 := eq58 X0 X0
       grind)
    | (have r₁ := eq5258 X1 X1
       have r₂ := eq58 X0 X1
       grind)
    | exact resolve eq5258 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5575 : ∀ X0 X1 : G, (τ (τ (τ X0))) ≠ (τ (τ (τ X0))) ∨ (M.op (τ (τ X0)) X1) = X1 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5258 (τ (τ X0)) X1
       have i₂ := eq939 (τ (τ X0)) X0
       grind)
    | exact superpose eq939 eq5258
    | (have j0 := eq5258 (τ (τ X0)) X1
       have j1 := eq939 X0 X0
       grind)
    | exact resolve eq5258 eq939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939 eq5258
  have eq5596 : ∀ X0 X1 : G, (M.op (τ (τ X0)) X1) = X1 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq5575 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5575
  have eq5598 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq5573 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5573
  have eq5608 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq5563 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5563
  have eq5620 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5598 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5598
    | (have j0 := eq5598 (σ X0) X1
       grind)
    | exact resolve eq5598 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5598
  have eq5793 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (M.op X1 X1) ≠ X1 ∨ (k X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq313 X1 X0
       have i₂ := eq5608 X1 X0
       grind)
    | exact superpose eq5608 eq313
    | (have j0 := eq313 X1 X1
       have j1 := eq5608 X1 X1
       grind)
    | (have r₁ := eq313 (σ X0) X1
       have r₂ := eq5608 X0 (σ X0)
       grind)
    | exact resolve eq313 eq5608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313 eq5608
  have eq5858 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (k X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have j0 := eq5793 X0 X1
       have j1 := eq2036 X0 (σ X1)
       grind)
    | (have r₁ := eq5793 X0 X1
       have r₂ := eq2036 X1 X1
       grind)
    | exact resolve eq5793 eq2036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2036 eq5793
  have eq6024 : ∀ X0 X2 : G, (M.op X0 X2) = X2 ∨ (M.op X2 X2) ≠ X2 := by
    intro X0 X2
    first
    | (have i₁ := eq5559 X2 (M.op X0 (M.op x X0)) X0
       have i₂ := eq285 x X0
       grind)
    | exact superpose eq285 eq5559
    | (have j0 := eq5559 X2 x X2
       grind)
    | exact resolve eq5559 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285 eq5559
  have eq6806 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (σ X0) ≠ (k (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5596 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5596
    | (have j0 := eq5596 (σ X0) X1
       grind)
    | exact resolve eq5596 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5596
  have eq6897 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6806 X0 X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq6806
    | (have j0 := eq6806 X0 X1
       grind)
    | exact resolve eq6806 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6806
  have eq6956 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (τ X0) ≠ (k (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5858 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5858
    | (have j0 := eq5858 X0 (τ X0)
       grind)
    | exact resolve eq5858 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5858
  have eq7066 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6956 X0 X1
       have i₂ := eq37 X0 X0
       grind)
    | exact superpose eq37 eq6956
    | (have j0 := eq6956 X0 X1
       grind)
    | exact resolve eq6956 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6956
  have eq7081 : ∀ X0 X1 : G, (τ (τ X0)) ≠ (τ (τ X0)) ∨ (τ X0) = (M.op X1 (τ X0)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7066 (τ X0) X1
       have i₂ := eq58 (τ X0) X0
       grind)
    | exact superpose eq58 eq7066
    | (have j0 := eq7066 (τ X0) X1
       have j1 := eq58 X0 X0
       grind)
    | (have r₁ := eq7066 X1 X1
       have r₂ := eq58 X0 X1
       grind)
    | exact resolve eq7066 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq7066
  have eq7106 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (τ X0)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq7081 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7081
  have eq8329 : ∀ X0 X1 : G, (σ (τ (τ (τ (τ X0))))) ≠ (σ (τ (τ (τ (τ X0))))) ∨ (M.op (τ (τ (τ (τ (τ X0))))) X1) = X1 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6897 (τ (τ (τ (τ X0)))) X1
       have i₂ := eq1978 X0 (τ (τ (τ (τ X0))))
       grind)
    | exact superpose eq1978 eq6897
    | (have j0 := eq6897 (τ (τ (τ (τ X0)))) X1
       have j1 := eq1978 X0 X1
       grind)
    | exact resolve eq6897 eq1978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1978 eq6897
  have eq8340 : ∀ X0 X1 : G, (M.op (τ (τ (τ (τ (τ X0))))) X1) = X1 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq8329 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8329
  have eq20138 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq677
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq677
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq677 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20141 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq20138
  have eq20143 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq155 x
       grind)
    | (have r₁ := eq20141
       have r₂ := eq155 x
       grind)
    | exact resolve eq20141 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq20141
  have eq20145 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq20143
       have r₂ := eq2424
       grind)
    | exact resolve eq20143 eq2424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20143
  have eq20164 : (σ x) ≠ (σ y) ∨ (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5501
       have i₂ := eq20145
       grind)
    | exact superpose eq20145 eq5501
    | exact resolve eq5501 eq20145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5501
  have eq20175 : ∀ X0 : G, y = (M.op x x) ∨ (M.op x X0) = X0 ∨ (σ x) ≠ (σ y) := by
    intro X0
    first
    | (have i₁ := eq5620 x X0
       have i₂ := eq20145
       grind)
    | exact superpose eq20145 eq5620
    | (have j0 := eq5620 x X0
       grind)
    | exact resolve eq5620 eq20145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20200 : (τ (σ x)) ≠ (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1042 (σ x)
       have i₂ := eq20145
       grind)
    | exact superpose eq20145 eq1042
    | exact resolve eq1042 eq20145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq20280 : y ≠ (τ (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq20200
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq20200
    | exact resolve eq20200 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20200
  have eq20286 : (σ x) ≠ (σ y) ∨ (σ y) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20175 eq20164
    | exact resolve eq20164 eq20175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20164 eq20175
  have eq20287 : y = (M.op x x) ∨ (σ x) ≠ (σ y) := by grind
  clear eq20286
  have eq20304 : x ≠ y ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq20280
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq20280
    | exact resolve eq20280 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20280
  have eq20311 : y = (M.op x x) ∨ x ≠ y := by
    first
    | (have r₁ := eq20304
       have r₂ := eq20287
       grind)
    | exact resolve eq20304 eq20287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20304
  have eq20323 : x ≠ y ∨ x ≠ y := by
    first
    | (have i₁ := eq2424
       have i₂ := eq20311
       grind)
    | exact superpose eq20311 eq2424
    | exact resolve eq2424 eq20311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20311
  have eq20407 : x ≠ y := by grind
  clear eq20323
  have eq20547 : (σ x) ≠ (σ y) ∨ x = y ∨ (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq1307 x
       have i₂ := eq20287
       grind)
    | exact superpose eq20287 eq1307
    | exact resolve eq1307 eq20287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1307 eq20287
  have eq20613 : (σ x) ≠ (σ y) ∨ x = y := by grind
  clear eq20547
  have eq20619 : (σ x) ≠ (σ y) := by
    first
    | (have r₁ := eq20613
       have r₂ := eq20407
       grind)
    | exact resolve eq20613 eq20407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20613
  have eq29638 : x = (k (τ (σ y)) x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq95 x
       have i₂ := eq20145
       grind)
    | exact superpose eq20145 eq95
    | exact resolve eq95 eq20145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq29777 : x = (k (τ (σ y)) x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq29638
       have r₂ := eq20619
       grind)
    | exact resolve eq29638 eq20619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29638
  have eq29813 : y = (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq29777
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq29777
    | exact resolve eq29777 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29777
  have eq29834 : x = (k y x) ∨ x = y ∨ x = (k y x) := by grind
  clear eq29813
  have eq29916 : x = (k y x) ∨ x = y := by grind
  clear eq29834
  have eq29921 : x = (k y x) := by
    first
    | (have r₁ := eq29916
       have r₂ := eq20407
       grind)
    | exact resolve eq29916 eq20407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29916
  have eq29922 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq677
       have i₂ := eq29921
       grind)
    | exact superpose eq29921 eq677
    | exact resolve eq677 eq29921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq29933 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq29921
       grind)
    | exact superpose eq29921 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq29921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29921
  have eq29946 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq29933
       have r₂ := eq2424
       grind)
    | exact resolve eq29933 eq2424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29933
  have eq29964 : x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq280 x
       have i₂ := eq29946
       grind)
    | exact superpose eq29946 eq280
    | exact resolve eq280 eq29946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq32186 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq703 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq703
    | (have j0 := eq703 X0
       have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq703 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32224 : ∀ X0 : G, (σ (τ X0)) = (M.op (k (σ (τ X0)) X0) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq703 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq703
    | (have j0 := eq703 (τ X0)
       grind)
    | exact resolve eq703 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq703
  have eq32334 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq32186 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32186
  have eq32382 : ∀ X0 : G, (σ (τ X0)) = (M.op (k (σ (τ X0)) X0) (σ (τ X0))) := by
    intro X0
    first
    | (have j0 := eq32224 X0
       have j1 := eq6024 (k (σ (τ X0)) X0) (σ (τ X0))
       grind)
    | (have r₁ := eq32224 X0
       have r₂ := eq6024 X0 (σ (τ X0))
       grind)
    | exact resolve eq32224 eq6024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6024 eq32224
  have eq32400 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq32334 X0
       have j1 := eq5620 (σ (M.op X0 X0)) (σ X0)
       grind)
    | (have r₁ := eq32334 X0
       have r₂ := eq5620 X0 x
       grind)
    | (have r₁ := eq32334 (σ X0)
       have r₂ := eq5620 X0 x
       grind)
    | exact resolve eq32334 eq5620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5620 eq32334
  have eq32411 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq32382 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32382
    | exact resolve eq32382 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32382
  have eq32414 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq32400 X0
       have j1 := eq5045 (σ (M.op X0 X0)) X0
       grind)
    | (have r₁ := eq32400 x
       have r₂ := eq5045 X0 x
       grind)
    | exact resolve eq32400 eq5045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5045 eq32400
  have eq32453 : ∀ X0 : G, (τ X0) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq32411 (τ X0)
       have i₂ := eq37 X0 X0
       grind)
    | exact superpose eq37 eq32411
    | exact resolve eq32411 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32411
  have eq32584 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq32414 x
       have i₂ := eq29946
       grind)
    | exact superpose eq29946 eq32414
    | exact resolve eq32414 eq29946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29946 eq32414
  have eq32832 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq32453 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq32453
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq32453 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32453
  have eq32939 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq32832 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32832
  have eq32967 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq32939 X0
       have j1 := eq7106 X0 (τ (M.op X0 X0))
       grind)
    | (have r₁ := eq32939 X0
       have r₂ := eq7106 X0 x
       grind)
    | exact resolve eq32939 eq7106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32939
  have eq33143 : (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq32967 (σ x)
       have i₂ := eq29922
       grind)
    | exact superpose eq29922 eq32967
    | exact resolve eq32967 eq29922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29922 eq32967
  have eq33242 : (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have j1 := eq7106 (σ x) (τ (σ y))
       grind)
    | (have r₁ := eq33143
       have r₂ := eq7106 (σ x) x
       grind)
    | exact resolve eq33143 eq7106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7106 eq33143
  have eq33272 : x = (M.op (τ (σ y)) x) ∨ (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq33242
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq33242
    | exact resolve eq33242 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33242
  have eq33275 : x = (M.op y x) ∨ (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq33272
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq33272
    | exact resolve eq33272 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33272
  have eq33277 : x = (M.op y x) ∨ (σ x) ≠ (σ x) := by
    first
    | exact superpose eq29964 eq33275
    | exact resolve eq33275 eq29964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29964 eq33275
  have eq33278 : x = (M.op y x) := by grind
  clear eq33277
  have eq33333 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq4975 X0 y x
       have i₂ := eq33278
       grind)
    | exact superpose eq33278 eq4975
    | (have j0 := eq4975 X0 x x
       grind)
    | exact resolve eq4975 eq33278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33278
  have eq37231 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) ≠ X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4975 X0 (σ y) (σ x)
       have i₂ := eq32584
       grind)
    | exact superpose eq32584 eq4975
    | (have j0 := eq4975 X0 x x
       grind)
    | exact resolve eq4975 eq32584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4975 eq32584
  have eq37241 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) ≠ X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq33333 eq37231
    | (have j0 := eq37231 X0
       have j1 := eq33333 X0
       grind)
    | exact resolve eq37231 eq33333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37231
  have eq37251 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have j0 := eq37241 X0
       grind)
    | (have r₁ := eq37241 X0
       have r₂ := eq20407
       grind)
    | exact resolve eq37241 eq20407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20407 eq37241
  have eq39791 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq37251 X0
       grind)
    | exact superpose eq37251 eq16
    | (have j1 := eq37251 X0
       grind)
    | exact resolve eq16 eq37251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37251
  have eq39854 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | exact superpose eq33333 eq39791
    | (have j0 := eq39791 X0
       have j1 := eq33333 X0
       grind)
    | exact resolve eq39791 eq33333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33333 eq39791
  have eq39855 : ∀ X0 : G, (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have j0 := eq39854 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39854
  have eq39916 : ∀ X0 : G, (τ (τ (τ (τ (τ X0))))) ≠ (τ (τ (τ (τ (τ X0))))) ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq39855 (τ (τ (τ (τ (τ X0)))))
       have i₂ := eq8340 X0 (τ (τ (τ (τ (τ X0)))))
       grind)
    | exact superpose eq8340 eq39855
    | (have j1 := eq8340 X0 x
       grind)
    | (have r₁ := eq39855 (τ (τ (τ (τ (τ X0)))))
       have r₂ := eq8340 X0 (τ (τ (τ (τ (τ X0)))))
       grind)
    | exact resolve eq39855 eq8340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8340
  have eq39936 : ∀ X0 : G, (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have j0 := eq39916 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39916
  have eq57985 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq215 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq215
    | (have j0 := eq215 X1 X1
       grind)
    | exact resolve eq215 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58139 : (τ (σ y)) = (k x (τ (σ x))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq215 (σ x) x
       have i₂ := eq20145
       grind)
    | exact superpose eq20145 eq215
    | exact resolve eq215 eq20145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq20145
  have eq58321 : (τ (σ y)) = (k x (τ (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq58139
  have eq58400 : (τ (σ y)) = (k x (τ (σ x))) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq58321
       have r₂ := eq20619
       grind)
    | exact resolve eq58321 eq20619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20619 eq58321
  have eq58497 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq57985 X0 X1
       grind)
    | (have r₁ := eq57985 X0 X0
       have r₂ := eq39855 X0
       grind)
    | (have r₁ := eq57985 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       have r₂ := eq39855 (M.op X1 X1)
       grind)
    | (have r₁ := eq57985 X0 X0
       have r₂ := eq39855 X0
       grind)
    | exact resolve eq57985 eq39855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57985
  have eq58529 : (k x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq58400
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq58400
    | exact resolve eq58400 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58400
  have eq58614 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq58497 X0 X1
       have i₂ := eq37 X1 X0
       grind)
    | exact superpose eq37 eq58497
    | (have j0 := eq58497 X0 X1
       grind)
    | exact resolve eq58497 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq58497
  have eq58620 : y = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq58529
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq58529
    | exact resolve eq58529 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58529
  have eq58749 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq58620
       grind)
    | exact superpose eq58620 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq58620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58620
  have eq58764 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq58749
  have eq58767 : y = (M.op x x) := by
    first
    | (have r₁ := eq58764
       have r₂ := eq2424
       grind)
    | exact resolve eq58764 eq2424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2424 eq58764
  have eq58866 : y = (M.op x y) := by
    first
    | (have i₁ := eq305 x x
       have i₂ := eq58767
       grind)
    | exact superpose eq58767 eq305
    | exact resolve eq305 eq58767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58908 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq58866
       grind)
    | exact superpose eq58866 eq16
    | exact resolve eq16 eq58866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58866
  have eq60134 : ∀ X0 : G, (τ (σ X0)) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 (k X0 X0))
       have i₂ := eq1156 X0
       grind)
    | exact superpose eq1156 eq10
    | (have j1 := eq1156 X0
       grind)
    | exact resolve eq10 eq1156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156
  have eq60348 : ∀ X0 : G, (τ (σ X0)) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq60134 X0
       grind)
    | (have r₁ := eq60134 X0
       have r₂ := eq39855 X0
       grind)
    | exact resolve eq60134 eq39855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39855 eq60134
  have eq60410 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq60348 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq60348
    | (have j0 := eq60348 X0
       grind)
    | exact resolve eq60348 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60348
  have eq63768 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq58614 X1 X0
       grind)
    | exact superpose eq58614 eq11
    | (have j1 := eq58614 X1 X0
       grind)
    | exact resolve eq11 eq58614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58614
  have eq63908 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63768 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq63768
    | (have j0 := eq63768 X0 X1
       grind)
    | exact resolve eq63768 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63768
  have eq64196 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq60410 X0
       have i₂ := eq5256 X0 (k X0 X0)
       grind)
    | exact superpose eq5256 eq60410
    | (have j0 := eq60410 X0
       have j1 := eq5256 X0 x
       grind)
    | exact resolve eq60410 eq5256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5256 eq60410
  have eq64636 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq64196 X0
       have j1 := eq63908 X0 X0
       grind)
    | (have r₁ := eq64196 x
       have r₂ := eq63908 x x
       grind)
    | (have r₁ := eq64196 (M.op X0 X0)
       have r₂ := eq63908 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq64196 eq63908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63908 eq64196
  have eq64662 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq64636 X0
       grind)
    | (have r₁ := eq64636 X0
       have r₂ := eq39936 X0
       grind)
    | exact resolve eq64636 eq39936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39936 eq64636
  have eq66463 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq64662 (σ X0)
       grind)
    | exact superpose eq64662 eq15
    | exact resolve eq15 eq64662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66520 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66463 X0
       have i₂ := eq64662 X0
       grind)
    | exact superpose eq64662 eq66463
    | exact resolve eq66463 eq64662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64662 eq66463
  have eq69828 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq305 (σ X0) (σ X0)
       have i₂ := eq66520 X0
       grind)
    | exact superpose eq66520 eq305
    | exact resolve eq305 eq66520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305 eq66520
  have eq70693 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq69828 x
       have i₂ := eq58767
       grind)
    | exact superpose eq58767 eq69828
    | exact resolve eq69828 eq58767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58767 eq69828
  have eq70756 : False := by grind
  exact eq70756

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyy_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
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
  have eq51 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq52 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq55 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
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
  clear eq37
  have eq75 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq78 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq75 x
       grind)
    | exact superpose eq75 eq44
    | exact resolve eq44 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
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
  have eq81 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq78
       have i₂ := eq75 sF2
       grind)
    | exact superpose eq75 eq78
    | exact resolve eq78 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq78
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
  have eq584 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq591 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq584 X0
       grind)
    | exact superpose eq584 eq14
    | exact resolve eq14 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq1143 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq54 eq591
    | exact resolve eq591 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1146 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq55 eq591
    | exact resolve eq591 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq10021 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq10022 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq10021
    | exact resolve eq10021 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10021
  have eq10033 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq10022
       have r₂ := eq28
       grind)
    | exact resolve eq10022 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10022
  have eq10037 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq10033 eq80
    | exact resolve eq80 eq10033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10033
  have eq10122 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq10037
    | exact resolve eq10037 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10037
  have eq10123 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10122
  have eq10134 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq81
       have i₂ := eq10123
       grind)
    | exact superpose eq10123 eq81
    | exact resolve eq81 eq10123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq10142 : y = (M.op (M.op (M.op x y) x) y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq51 x
       have i₂ := eq10123
       grind)
    | exact superpose eq10123 eq51
    | exact resolve eq51 eq10123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq10143 : x = (M.op (M.op x (M.op x y)) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq10123
       grind)
    | exact superpose eq10123 eq54
    | exact resolve eq54 eq10123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq10123
  have eq10215 : x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1143 eq10143
    | exact resolve eq10143 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143 eq10143
  have eq10223 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10134
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10134
    | exact resolve eq10134 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10134
  have eq10601 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10223 eq52
    | exact resolve eq52 eq10223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq10602 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10223 eq55
    | exact resolve eq55 eq10223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq10223
  have eq10670 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1146 eq10602
    | exact resolve eq10602 eq1146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146 eq10602
  have eq11980 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10215 eq10142
    | exact resolve eq10142 eq10215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10142 eq10215
  have eq12007 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11980
  have eq12008 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12007
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12007
    | exact resolve eq12007 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12007
  have eq12244 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12008 eq30
    | exact resolve eq30 eq12008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12008
  have eq12368 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq12244
    | exact resolve eq12244 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12244
  have eq12369 : y = (M.op x y) ∨ x = y := by grind
  clear eq12368
  have eq12392 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq12369 eq21
    | exact resolve eq21 eq12369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12369
  have eq12525 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12392
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12392
    | exact resolve eq12392 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12392
  have eq36344 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10670 eq10601
    | exact resolve eq10601 eq10670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10601 eq10670
  have eq36382 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq36344
  have eq36383 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq36382
    | exact resolve eq36382 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36382
  have eq36384 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq36383 eq28
    | exact resolve eq28 eq36383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36383
  have eq36423 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq36384
       have r₂ := eq12525
       grind)
    | exact resolve eq36384 eq12525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12525 eq36384
  have eq36723 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq36423 eq30
    | exact resolve eq30 eq36423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq36423
  have eq36984 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq36723
    | exact resolve eq36723 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq36723
  have eq36985 : x = y := by grind
  clear eq36984
  have eq37012 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq36985
       grind)
    | exact superpose eq36985 eq19
    | exact resolve eq19 eq36985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq37013 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq36985
       grind)
    | exact superpose eq36985 eq25
    | exact resolve eq25 eq36985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq36985
  have eq37154 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq37013
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37013
    | exact resolve eq37013 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq37013
  have eq37182 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq37154 eq27
    | exact resolve eq27 eq37154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq37154
  have eq37590 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq37182 eq80
    | exact resolve eq80 eq37182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq37182
  have eq37687 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq37590
       have i₂ := eq37012
       grind)
    | exact superpose eq37012 eq37590
    | exact resolve eq37590 eq37012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37012 eq37590
  have eq38283 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37687 eq15
    | exact resolve eq15 eq37687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37687
  have eq38362 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq38283
    | exact resolve eq38283 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq38283
  have eq38383 : False := by grind
  exact eq38383

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyx_pyx_pxx_pxy_Equation2725 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op (M.op X1 X0) (M.op X2 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq65 (σ X0)
       grind)
    | exact superpose eq65 eq10
    | exact resolve eq10 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq67
    | exact resolve eq67 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq131 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq134 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq131
       have i₂ := eq65 sF1
       grind)
    | exact superpose eq65 eq131
    | exact resolve eq131 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq136 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq134
       have i₂ := eq65 sF0
       grind)
    | exact superpose eq65 eq134
    | exact resolve eq134 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq134
  have eq545 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 (M.op X0 X0) X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X1 X1)
       have i₂ := eq53 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq566 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq545 X1 (σ X0)
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq545
    | exact resolve eq545 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq655 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X0 (M.op X1 X1))) (M.op X3 X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 (M.op X0 (M.op X1 X1)) X2 X3 (M.op X0 X0)
       have i₂ := eq52 X0 X0 X0 X1
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) (M.op X3 X3)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X0 (M.op X4 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X1 (M.op (M.op X1 X0) (M.op X3 X3)) X4 X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op X1 X1)) = (M.op (M.op (σ x) (M.op X0 X0)) (M.op (σ y) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq678 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 X1 (M.op X1 X1) X2
       have i₂ := eq53 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq711 : ∀ X0 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq566 X2 x
       have i₂ := eq566 X0 x
       grind)
    | exact superpose eq566 eq566
    | exact resolve eq566 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq768 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 X1
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq76
    | (have j0 := eq76 X0 X1
       grind)
    | exact resolve eq76 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq769 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq768 X0 X1
       have i₂ := eq72 X1
       grind)
    | exact superpose eq72 eq768
    | (have j0 := eq768 X0 X1
       grind)
    | exact resolve eq768 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq774 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq769 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq769
    | exact resolve eq769 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq881 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq774 X0 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq774
    | (have j0 := eq774 X0 X1
       grind)
    | exact resolve eq774 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq774
  have eq1279 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ (M.op X0 X0))) (M.op X2 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq678 X2 X1 (σ X0)
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq678
    | exact resolve eq678 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq4775 : ∀ X0 X1 X3 : G, (M.op (σ x) (M.op X1 X1)) = (M.op (σ y) (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X3 X3))) := by
    intro X0 X1 X3
    first
    | exact superpose eq665 eq655
    | exact resolve eq655 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq4785 : ∀ X1 : G, (M.op (σ x) (M.op X1 X1)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X1
    first
    | (have i₁ := eq4775 x X1 x
       have i₂ := eq678 x sF4 x
       grind)
    | exact superpose eq678 eq4775
    | exact resolve eq4775 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4775
  have eq5087 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (σ x) (M.op X0 X0)) (M.op (σ y) (M.op X1 X1))) (M.op X3 X3)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X4 X4)) (M.op (M.op X2 X2) (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | exact superpose eq665 eq662
    | exact resolve eq662 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq5218 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq662 (M.op X0 X1) X1 x X2 x
       have i₂ := eq52 X1 X0 x x
       grind)
    | exact superpose eq52 eq662
    | exact resolve eq662 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq662
  have eq5583 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op (M.op (σ x) (M.op X0 X0)) (M.op (σ y) (M.op X1 X1))) (M.op X3 X3)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X4 X4)) (M.op X5 X5)) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq5087 X0 X1 x X3 X4 X5
       have i₂ := eq560 x (M.op X5 X5)
       grind)
    | exact superpose eq560 eq5087
    | exact resolve eq5087 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5087
  have eq5651 : ∀ X0 X1 X3 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (M.op X0 X0)) (M.op (σ y) (M.op X1 X1))) (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq5583 X0 X1 X3 x X0
       have i₂ := eq678 X0 sF4 x
       grind)
    | exact superpose eq678 eq5583
    | exact resolve eq5583 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678 eq5583
  have eq5679 : ∀ X1 X3 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op X1 X1))) (M.op X3 X3)) := by
    intro X1 X3
    first
    | exact superpose eq4785 eq5651
    | exact resolve eq5651 eq4785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5651
  have eq10994 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq881 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq10998 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) X1) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq10994 X0 X1
       grind)
    | (have r₁ := eq10994 X0 X1
       have r₂ := eq711 X0 (τ X1)
       grind)
    | (have r₁ := eq10994 x X1
       have r₂ := eq711 (τ X1) x
       grind)
    | exact resolve eq10994 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq10994
  have eq101304 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X1 (σ (M.op X0 X0))) (M.op X2 X2)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5218 (σ X0) X1 X2
       have i₂ := eq10998 X0 X1
       grind)
    | exact superpose eq10998 eq5218
    | (have j1 := eq10998 X0 X1
       grind)
    | exact resolve eq5218 eq10998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5218 eq10998
  have eq101484 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (k X1 (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq101304 X0 X1 x
       have i₂ := eq1279 X0 X1 x
       grind)
    | exact superpose eq1279 eq101304
    | (have j0 := eq101304 X0 X1 x
       grind)
    | exact resolve eq101304 eq1279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1279 eq101304
  have eq159421 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq101484 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq101484
    | exact resolve eq101484 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101484
  have eq160834 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq159421 y x
       grind)
    | exact superpose eq159421 eq44
    | (have j1 := eq159421 (σ (M.op x y)) (k (σ x) (σ y))
       grind)
    | exact resolve eq44 eq159421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq161126 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq160834
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq160834
    | exact resolve eq160834 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160834
  have eq161306 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq161126
    | exact resolve eq161126 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161126
  have eq162077 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq161306 eq159421
    | (have j0 := eq159421 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq159421 eq161306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159421 eq161306
  have eq162084 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq162077
    | exact resolve eq162077 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq162077
  have eq162097 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq162084
       have r₂ := eq27
       grind)
    | exact resolve eq162084 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162084
  have eq162103 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq162097 eq29
    | exact resolve eq29 eq162097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq162097
  have eq162308 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq162103
    | exact resolve eq162103 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq162103
  have eq162309 : x = y := by grind
  clear eq162308
  have eq162339 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq162309
       grind)
    | exact superpose eq162309 eq18
    | exact resolve eq18 eq162309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq162340 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq162309
       grind)
    | exact superpose eq162309 eq24
    | exact resolve eq24 eq162309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq162309
  have eq162652 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq162340
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq162340
    | exact resolve eq162340 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq162340
  have eq162999 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq162339
       have i₂ := eq545 X0 x
       grind)
    | (have i₁ := eq162339
       have i₂ := eq545 x X0
       grind)
    | exact superpose eq545 eq162339
    | exact resolve eq162339 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq163186 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op X0 X0))) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq5679 X0 x
       have i₂ := eq162339
       grind)
    | exact superpose eq162339 eq5679
    | exact resolve eq5679 eq162339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5679 eq162339
  have eq163439 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op X0 X0))) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq162652 eq163186
    | exact resolve eq163186 eq162652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163186
  have eq163595 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op x y)) := by
    first
    | exact superpose eq4785 eq163439
    | exact resolve eq163439 eq4785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4785 eq163439
  have eq163668 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) (M.op x y)) := by
    first
    | exact superpose eq162652 eq163595
    | exact resolve eq163595 eq162652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162652 eq163595
  have eq163694 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq163668
       have i₂ := eq560 (M.op sF2 sF4) sF0
       grind)
    | exact superpose eq560 eq163668
    | exact resolve eq163668 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560 eq163668
  have eq163700 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq163694 eq27
    | exact resolve eq27 eq163694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq163694
  have eq164440 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq136
       have i₂ := eq162999 sF0
       grind)
    | exact superpose eq162999 eq136
    | exact resolve eq136 eq162999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq164575 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq164440
       have i₂ := eq162999 sF1
       grind)
    | exact superpose eq162999 eq164440
    | exact resolve eq164440 eq162999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162999 eq164440
  have eq165138 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq164575
    | exact resolve eq164575 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq164575
  have eq166000 : False := by grind
  exact eq166000

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_y_pyy_pxy_Equation2725 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  clear eq36
  have eq47 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op X0 X0)) x) := by
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
  have eq48 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op (M.op X1 X0) (M.op X2 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq67 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq71 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq67
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq67
    | exact resolve eq67 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq71
    | exact resolve eq71 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq343 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 (M.op X0 X0) X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X1 X1)
       have i₂ := eq50 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq364 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    grind
  clear eq343
  have eq416 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X0 (M.op X1 X1))) (M.op X3 X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq49 (M.op X0 (M.op X1 X1)) X2 X3 (M.op X0 X0)
       have i₂ := eq49 X0 X0 X0 X1
       grind)
    | exact superpose eq49 eq49
    | exact resolve eq49 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) (M.op X3 X3)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X0 (M.op X4 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 X1 (M.op (M.op X1 X0) (M.op X3 X3)) X4 X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X1 X1)) = (M.op (M.op x (M.op X0 X0)) (M.op y (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq47 eq49
    | exact resolve eq49 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq426 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op X1 X1)) = (M.op (M.op (σ x) (M.op X0 X0)) (M.op (σ y) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq48 eq49
    | exact resolve eq49 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X1 X1 (M.op X1 X1) X2
       have i₂ := eq50 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq625 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X0)) = (σ (k X2 X2)) ∨ (M.op X0 (M.op (M.op X1 X1) X0)) = (σ X2) ∨ (M.op X0 (M.op (M.op X1 X1) X0)) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X0 X0
       have i₂ := eq50 X0 X1 (σ X0)
       grind)
    | exact superpose eq50 eq63
    | exact resolve eq63 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq632 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X2) X1)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 X1 X2 (σ X0)
       have i₂ := eq63 X0 X0
       grind)
    | exact superpose eq63 eq50
    | (have j1 := eq63 X0 X0
       grind)
    | exact resolve eq50 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq644 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq63 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq645 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq644 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq654 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X2) X1)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq632 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq661 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X0)) = (σ (k X2 X2)) ∨ (M.op X0 (M.op (M.op X1 X1) X0)) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq625 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq665 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq654 X0 X1 x
       have i₂ := eq356 x X1
       grind)
    | exact superpose eq356 eq654
    | (have j0 := eq654 X0 X1 x
       grind)
    | exact resolve eq654 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq667 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (k X2 X2)) ∨ (M.op X0 (M.op (M.op X1 X1) X0)) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq661 X0 X1 X2
       have i₂ := eq356 X1 X0
       grind)
    | exact superpose eq356 eq661
    | (have j0 := eq661 X0 X1 X2
       grind)
    | exact resolve eq661 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq677 : ∀ X0 X2 : G, (M.op X0 X0) = (σ (k X2 X2)) ∨ (M.op X0 X0) = (σ X2) := by
    intro X0 X2
    first
    | (have i₁ := eq667 X0 x X2
       have i₂ := eq356 x X0
       grind)
    | exact superpose eq356 eq667
    | (have j0 := eq667 X0 x X2
       grind)
    | exact resolve eq667 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq2687 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq677 X1 (M.op X0 X0)
       have i₂ := eq364 X0 (M.op X0 X0)
       grind)
    | exact superpose eq364 eq677
    | (have j0 := eq677 X1 (M.op X0 X0)
       grind)
    | exact resolve eq677 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364 eq677
  have eq2773 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2687 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2687
  have eq2896 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X1 X1)
       have i₂ := eq2773 X1 X0
       grind)
    | exact superpose eq2773 eq16
    | exact resolve eq16 eq2773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3238 : ∀ X0 X2 : G, (M.op (τ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq356 x X2
       have i₂ := eq2896 X0 x
       grind)
    | exact superpose eq2896 eq356
    | exact resolve eq356 eq2896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2896
  have eq5341 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq645 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq645
    | (have j0 := eq645 (τ X0)
       grind)
    | exact resolve eq645 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq645
  have eq5358 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5341 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5341
    | (have j0 := eq5341 X0
       grind)
    | exact resolve eq5341 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5341
  have eq5368 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5358 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5358
    | (have j0 := eq5358 X0
       grind)
    | exact resolve eq5358 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5358
  have eq5441 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ (k x x)) := by
    intro X0
    first
    | (have i₁ := eq665 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq665
    | (have j0 := eq665 x X0
       grind)
    | exact resolve eq665 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq5522 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq5441 X0
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq5441
    | exact resolve eq5441 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq5441
  have eq5635 : ∀ X0 X1 X3 : G, (M.op x (M.op X1 X1)) = (M.op y (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X3 X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq416 y x (M.op x (M.op X1 X1)) X3
       have i₂ := eq425 X1 X0 x
       grind)
    | exact superpose eq425 eq416
    | exact resolve eq416 eq425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq5644 : ∀ X1 : G, (M.op y (M.op x y)) = (M.op x (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq5635 x X1 x
       have i₂ := eq437 x sF0 x
       grind)
    | exact superpose eq437 eq5635
    | exact resolve eq5635 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5635
  have eq5686 : ∀ X1 : G, x = (M.op (M.op y (M.op x y)) (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq437 X1 x x
       have i₂ := eq5644 x
       grind)
    | exact superpose eq5644 eq437
    | exact resolve eq437 eq5644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5821 : ∀ X0 X1 X3 : G, (M.op (σ x) (M.op X1 X1)) = (M.op (σ y) (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X3 X3))) := by
    intro X0 X1 X3
    first
    | exact superpose eq426 eq416
    | exact resolve eq416 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq5830 : ∀ X1 : G, (M.op (σ x) (M.op X1 X1)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X1
    first
    | (have i₁ := eq5821 x X1 x
       have i₂ := eq437 x sF4 x
       grind)
    | exact superpose eq437 eq5821
    | exact resolve eq5821 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5821
  have eq5872 : ∀ X1 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op X1 X1)) := by
    intro X1
    first
    | exact superpose eq5830 eq437
    | exact resolve eq437 eq5830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5830
  have eq6543 : ∀ X0 X1 X2 X3 X5 : G, (M.op X0 (M.op X3 X3)) = (M.op X1 (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq416 X1 x (M.op X0 (M.op X3 X3)) X5
       have i₂ := eq423 X1 X0 X3 X2 x
       grind)
    | (have i₁ := eq416 (M.op X1 X1) X1 (M.op X1 X0) X3
       have i₂ := eq423 X0 X1 X2 (M.op X1 X1) x
       grind)
    | exact superpose eq423 eq416
    | exact resolve eq416 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416 eq423
  have eq6688 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X3 X3)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq6543 X0 X1 x X3 x
       have i₂ := eq437 x (M.op X0 X1) x
       grind)
    | exact superpose eq437 eq6543
    | exact resolve eq6543 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437 eq6543
  have eq15445 : ∀ X1 : G, x = (M.op X1 (M.op (M.op y (M.op x y)) X1)) := by
    intro X1
    first
    | exact superpose eq5686 eq6688
    | exact resolve eq6688 eq5686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15446 : ∀ X1 : G, (σ x) = (M.op X1 (M.op (M.op (σ y) (M.op (σ x) (σ y))) X1)) := by
    intro X1
    first
    | exact superpose eq5872 eq6688
    | exact resolve eq6688 eq5872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15453 : ∀ X1 : G, (M.op y (M.op x y)) = (M.op X1 (M.op x X1)) := by
    intro X1
    first
    | (have i₁ := eq6688 x X1 x
       have i₂ := eq5644 x
       grind)
    | exact superpose eq5644 eq6688
    | exact resolve eq6688 eq5644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5644
  have eq15713 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq48 x
       have i₂ := eq6688 sF4 x x
       grind)
    | (have i₁ := eq48 sF4
       have i₂ := eq6688 sF4 sF4 x
       grind)
    | exact superpose eq6688 eq48
    | exact resolve eq48 eq6688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq6688
  have eq16583 : (σ y) = (M.op (M.op (M.op x (M.op (σ x) (σ y))) (M.op y (M.op x y))) (σ x)) := by
    first
    | (have i₁ := eq15713 (M.op x sF4)
       have i₂ := eq15453 sF4
       grind)
    | exact superpose eq15453 eq15713
    | exact resolve eq15713 eq15453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15453 eq15713
  have eq16749 : (σ x) = (M.op (M.op (M.op y (M.op x y)) (M.op (σ y) (M.op (σ x) (σ y)))) x) := by
    first
    | exact superpose eq15445 eq15446
    | exact resolve eq15446 eq15445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16797 : x = (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op y (M.op x y))) (σ x)) := by
    first
    | exact superpose eq15446 eq15445
    | exact resolve eq15445 eq15446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15445 eq15446
  have eq25034 : ∀ X0 : G, (σ x) ≠ (M.op X0 X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq5522 eq5368
    | (have j0 := eq5368 (σ x)
       grind)
    | exact resolve eq5368 eq5522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5368 eq5522
  have eq25045 : ∀ X0 : G, (σ x) ≠ (M.op X0 X0) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq25034 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25034
  have eq25110 : ∀ X0 : G, (σ x) ≠ (σ (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq25045 x
       have i₂ := eq2773 X0 x
       grind)
    | exact superpose eq2773 eq25045
    | exact resolve eq25045 eq2773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2773 eq25045
  have eq30391 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq73 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30392 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq30391
    | exact resolve eq30391 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30391
  have eq30397 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq30392
       have r₂ := eq28
       grind)
    | exact resolve eq30392 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30392
  have eq30399 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq30397
    | exact resolve eq30397 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq30397
  have eq30404 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq30399
  have eq31124 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30404 eq73
    | exact resolve eq73 eq30404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq30404
  have eq31136 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq31124
  have eq31298 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq356 y X0
       have i₂ := eq31136
       grind)
    | exact superpose eq31136 eq356
    | exact resolve eq356 eq31136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356 eq31136
  have eq32250 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19
       have i₂ := eq31298 y
       grind)
    | exact superpose eq31298 eq19
    | (have j1 := eq31298 y
       grind)
    | exact resolve eq19 eq31298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31298
  have eq32428 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq32250
  have eq32520 : (σ x) = (M.op (M.op (M.op y (M.op x y)) (M.op (σ y) (σ y))) x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32428 eq16749
    | exact resolve eq16749 eq32428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16749 eq32428
  have eq32535 : (σ x) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5686 eq32520
    | exact resolve eq32520 eq5686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5686 eq32520
  have eq32751 : ∀ X0 : G, (M.op (τ (σ x)) X0) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3238 x X0
       have i₂ := eq32535
       grind)
    | exact superpose eq32535 eq3238
    | exact resolve eq3238 eq32535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3238 eq32535
  have eq32876 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq32751
    | exact resolve eq32751 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq32751
  have eq34358 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq32876 y
       grind)
    | exact superpose eq32876 eq19
    | (have j1 := eq32876 y
       grind)
    | exact resolve eq19 eq32876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq32876
  have eq34538 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq34358
  have eq34610 : y = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34538 eq30
    | exact resolve eq30 eq34538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq34538
  have eq34675 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq34610
    | exact resolve eq34610 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq34610
  have eq34676 : y = (M.op x y) := by grind
  clear eq34675
  have eq34677 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq34676 eq21
    | exact resolve eq21 eq34676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq34756 : x = (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op y y)) (σ x)) := by
    first
    | exact superpose eq34676 eq16797
    | exact resolve eq16797 eq34676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16797
  have eq34760 : x = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5872 eq34756
    | exact resolve eq34756 eq5872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5872 eq34756
  have eq34824 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq34677
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq34677
    | exact resolve eq34677 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq34677
  have eq35030 : (σ x) ≠ (σ x) ∨ x = (σ x) := by
    first
    | exact superpose eq34760 eq25110
    | exact resolve eq25110 eq34760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25110 eq34760
  have eq35064 : x = (σ x) := by
    first
    | (have r₁ := eq35030
       have r₂ := eq23
       grind)
    | exact resolve eq35030 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq35030
  have eq35228 : (σ y) = (M.op (M.op (M.op x (M.op (σ x) (σ y))) (M.op y (M.op x y))) x) := by
    first
    | exact superpose eq35064 eq16583
    | exact resolve eq16583 eq35064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16583 eq35064
  have eq35259 : (σ y) = (M.op (M.op (M.op x (M.op (σ x) (σ y))) (M.op y y)) x) := by
    first
    | exact superpose eq34676 eq35228
    | exact resolve eq35228 eq34676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34676 eq35228
  have eq35297 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35259
       have i₂ := eq14 sF4 x y
       grind)
    | exact superpose eq14 eq35259
    | exact resolve eq35259 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35259
  have eq35312 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34824 eq35297
    | exact resolve eq35297 eq34824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34824 eq35297
  have eq35324 : False := by grind
  exact eq35324
