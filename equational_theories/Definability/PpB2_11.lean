import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxy_pxx_pxy_Equation2046 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2046 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X2 X0)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 (M.op X0 X1) (M.op X1 X0)
       grind)
    | exact resolve eq11 eq13
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
  have eq175 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, y = (M.op (M.op (M.op y y) X0) (M.op x y)) := by
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
  have eq183 : ∀ X0 : G, y = (M.op (M.op (k y y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq175 y
       grind)
    | exact superpose eq175 eq178
    | exact resolve eq178 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq187 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) X1) (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) X1) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 : G, (k (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 (M.op X0 X0)
       have i₂ := eq175 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 : G, (k (M.op (k X0 X0) X0) (M.op (k X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq189 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq189
    | exact resolve eq189 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq650 : ∀ X0 X1 : G, (M.op (k X0 X0) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq188 (M.op (k X0 X0) X0) X1
       have i₂ := eq192 X0
       grind)
    | exact superpose eq192 eq188
    | exact resolve eq188 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq660 : (M.op (k x x) x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq650 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq650
    | (have j0 := eq650 x y
       grind)
    | exact resolve eq650 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661 : (M.op (k (σ x) (σ x)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq650
    | (have j0 := eq650 (σ x) (σ y)
       grind)
    | exact resolve eq650 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq684 : ∀ X0 : G, x = (M.op (M.op (M.op x y) x) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq187 x x X0
       have i₂ := eq660
       grind)
    | exact superpose eq660 eq187
    | exact resolve eq187 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq690 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq661 eq187
    | exact resolve eq187 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq661
  have eq711 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq712 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq936 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq711
       grind)
    | exact superpose eq711 eq41
    | exact resolve eq41 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq937 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq936
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq936
    | exact resolve eq936 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq939 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq937
    | exact resolve eq937 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq947 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq939 eq712
    | exact resolve eq712 eq939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq954 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq947
       have r₂ := eq27
       grind)
    | exact resolve eq947 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq959 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq954 eq690
    | exact resolve eq690 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq961 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq954 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq954
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq954
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq954
       grind)
    | exact resolve eq12 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq968 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq961
       have r₂ := eq26
       grind)
    | exact resolve eq961 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq961
  have eq970 : (σ x) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq959
       have i₂ := eq650 sF4 sF2
       grind)
    | exact superpose eq650 eq959
    | exact resolve eq959 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959
  have eq972 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq968
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq968
    | exact resolve eq968 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968
  have eq974 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq939 eq972
    | exact resolve eq972 eq939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939 eq972
  have eq977 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq970 eq192
    | exact resolve eq192 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq970
  have eq1044 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq974 eq977
    | exact resolve eq977 eq974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974 eq977
  have eq1055 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq1044
  have eq1062 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1055
       have r₂ := eq27
       grind)
    | exact resolve eq1055 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055
  have eq1068 : x = (M.op (M.op (M.op x y) x) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq684 y
       have i₂ := eq1062
       grind)
    | exact superpose eq1062 eq684
    | exact resolve eq684 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq1075 : (M.op (k y y) y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq650 y x
       have i₂ := eq1062
       grind)
    | exact superpose eq1062 eq650
    | exact resolve eq650 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq1079 : x = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1068
       have i₂ := eq650 sF0 x
       grind)
    | exact superpose eq650 eq1068
    | exact resolve eq1068 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq1252 : y = (M.op (M.op (M.op x y) y) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq183 y
       have i₂ := eq1075
       grind)
    | exact superpose eq1075 eq183
    | exact resolve eq183 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq1075
  have eq1264 : y = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1252
       have i₂ := eq650 sF0 y
       grind)
    | exact superpose eq650 eq1252
    | exact resolve eq1252 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650 eq1252
  have eq1266 : (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1079 eq1264
    | exact resolve eq1264 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079 eq1264
  have eq1268 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1266 eq32
    | exact resolve eq32 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1266
  have eq1297 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq1268
    | exact resolve eq1268 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1268
  have eq1298 : x = y := by grind
  clear eq1297
  have eq1432 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1298
       grind)
    | exact superpose eq1298 eq24
    | exact resolve eq24 eq1298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1439 : (M.op x y) = (k x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq711
       have i₂ := eq1298
       grind)
    | exact superpose eq1298 eq711
    | exact resolve eq711 eq1298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq1298
  have eq1443 : (M.op x y) = (k x x) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq1439
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq1439
    | exact resolve eq1439 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439
  have eq1444 : (M.op x y) = (k x x) := by grind
  clear eq1443
  have eq1447 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1432
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1432
    | exact resolve eq1432 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1432
  have eq1464 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1447 eq712
    | exact resolve eq712 eq1447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712 eq1447
  have eq1469 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1464
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq1464
    | exact resolve eq1464 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq1464
  have eq1470 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1469
  have eq1488 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1444
       grind)
    | exact superpose eq1444 eq40
    | exact resolve eq40 eq1444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1444
  have eq1495 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1488
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1488
    | exact resolve eq1488 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1488
  have eq1500 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1470 eq1495
    | exact resolve eq1495 eq1470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470 eq1495
  have eq1504 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1500
    | exact resolve eq1500 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1500
  have eq1506 : False := by grind
  exact eq1506

/-- `Equation2055`: `x = ((x ◇ y) ◇ x) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_pyx_y_pxy_Equation2055 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2055 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2055.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X1 X2)) = X0 := by
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
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq175 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 X0) X0 X1
       have i₂ := eq16 X0 X0 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : y ≠ (M.op x y) ∨ (k x y) = (M.op y x) := by
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
  have eq194 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq177 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 x y
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 (M.op X0 X1) X2
       have i₂ := eq177 X0 X1
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : x ≠ (M.op x (M.op x y)) ∨ (k x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq194
       grind)
    | exact superpose eq194 eq13
    | exact resolve eq13 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq630 : y ≠ (M.op x y) ∨ x = (M.op y x) ∨ x = (k y x) := by
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
  have eq647 : (M.op x y) = (k x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
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
  have eq648 : (k x x) = (M.op x (M.op x y)) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq194
       grind)
    | exact superpose eq194 eq11
    | exact resolve eq11 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq649 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq653 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
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
  have eq702 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : (k x x) = (M.op x (M.op x y)) ∨ x = (M.op x (M.op x y)) := by grind
  clear eq648
  have eq736 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq653 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq653 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq653 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq653 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq738 : (k x x) = (M.op x (M.op x y)) := by
    first
    | (have r₁ := eq709
       have r₂ := eq202
       grind)
    | exact resolve eq709 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq709
  have eq746 : (M.op x x) = (M.op x (k x x)) := by
    first
    | exact superpose eq738 eq177
    | exact resolve eq177 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq750 : (M.op x (M.op x y)) = (M.op x (k x x)) := by
    first
    | (have i₁ := eq746
       have i₂ := eq194
       grind)
    | exact superpose eq194 eq746
    | exact resolve eq746 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq746
  have eq752 : (k x x) = (M.op x (k x x)) := by
    first
    | exact superpose eq738 eq750
    | exact resolve eq750 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq766 : (k x x) ≠ (k x x) ∨ (M.op (k x x) x) = (k x (k x x)) := by
    first
    | (have i₁ := eq13 x (k x x)
       have i₂ := eq752
       grind)
    | exact superpose eq752 eq13
    | (have j0 := eq13 x (k x x)
       grind)
    | (have r₁ := eq13 x (k x x)
       have r₂ := eq752
       grind)
    | exact resolve eq13 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq769 : (M.op (k x x) x) = (k x (k x x)) := by grind
  clear eq766
  have eq1008 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq647
       grind)
    | exact superpose eq647 eq40
    | exact resolve eq40 eq647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1009 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1008
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1008
    | exact resolve eq1008 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1011 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq1009
    | exact resolve eq1009 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009
  have eq1167 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1011 eq649
    | exact resolve eq649 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq1174 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1167
       have r₂ := eq27
       grind)
    | exact resolve eq1167 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167
  have eq1181 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1174 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1174
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1174
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1174
       grind)
    | exact resolve eq12 eq1174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174
  have eq1189 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq1181
  have eq1194 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1189
    | exact resolve eq1189 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189
  have eq1195 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq1194
  have eq1227 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1195 eq90
    | exact resolve eq90 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq1195
  have eq1234 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq1227
    | exact resolve eq1227 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227
  have eq1237 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq647 eq1234
    | exact resolve eq1234 eq647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647 eq1234
  have eq1238 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1237
  have eq1268 : x ≠ x ∨ y = (M.op x y) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1238
       grind)
    | exact superpose eq1238 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1238
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1238
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1238
       grind)
    | exact resolve eq12 eq1238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1269 : x ≠ x ∨ (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1238
       grind)
    | exact superpose eq1238 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1238
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1238
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1238
       grind)
    | exact resolve eq13 eq1238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238
  have eq1275 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1269
  have eq1276 : y = (M.op x y) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1268
  have eq1280 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1275
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1275
    | exact resolve eq1275 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1275
  have eq1281 : y = (M.op x y) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1276
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1276
    | exact resolve eq1276 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276
  have eq1282 : y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1281
  have eq1308 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1280
       grind)
    | exact superpose eq1280 eq39
    | exact resolve eq39 eq1280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280
  have eq1311 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1308
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1308
    | exact resolve eq1308 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308
  have eq1313 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq1311
    | exact resolve eq1311 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1311
  have eq1317 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq1282
       grind)
    | exact superpose eq1282 eq35
    | exact resolve eq35 eq1282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1282
  have eq1326 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1317
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1317
    | exact resolve eq1317 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1317
  have eq1380 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1326 eq649
    | exact resolve eq649 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326
  have eq1388 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1380
  have eq1440 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1388 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1388
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1388
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1388
       grind)
    | exact resolve eq13 eq1388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1388
  have eq1446 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1440
  have eq1451 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1446
    | exact resolve eq1446 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446
  have eq1454 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1313 eq1451
    | exact resolve eq1451 eq1313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313 eq1451
  have eq1456 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1454
       have r₂ := eq27
       grind)
    | exact resolve eq1454 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1454
  have eq1463 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1456 eq195
    | exact resolve eq195 eq1456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq1469 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1463
    | exact resolve eq1463 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1463
  have eq1471 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1456 eq1469
    | exact resolve eq1469 eq1456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1456 eq1469
  have eq1477 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1471 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1479 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1471 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq1471
       grind)
    | exact resolve eq13 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471
  have eq1485 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq1477
  have eq1490 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1485
       have r₂ := eq1479
       grind)
    | exact resolve eq1485 eq1479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479 eq1485
  have eq1498 : (τ (σ y)) = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1490 eq97
    | exact resolve eq97 eq1490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq1490
  have eq1507 : y = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq1498
    | exact resolve eq1498 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1498
  have eq1516 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq752
       have i₂ := eq1507
       grind)
    | exact superpose eq1507 eq752
    | exact resolve eq752 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq1517 : (k x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq769
       have i₂ := eq1507
       grind)
    | exact superpose eq1507 eq769
    | exact resolve eq769 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769 eq1507
  have eq1533 : (k x y) = (M.op y x) := by
    first
    | (have r₁ := eq1517
       have r₂ := eq181
       grind)
    | exact resolve eq1517 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517
  have eq1534 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1516
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1516
    | exact resolve eq1516 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1516
  have eq1535 : y = (M.op x y) := by grind
  clear eq1534
  have eq1541 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1535
       grind)
    | exact superpose eq1535 eq18
    | exact resolve eq18 eq1535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1542 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1535
       grind)
    | exact superpose eq1535 eq24
    | exact resolve eq24 eq1535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1543 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (k (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq1535
       grind)
    | exact superpose eq1535 eq36
    | exact resolve eq36 eq1535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1544 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq1535
       grind)
    | exact superpose eq1535 eq40
    | exact resolve eq40 eq1535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq1546 : (M.op x y) ≠ (M.op x y) ∨ (k x (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq181
       have i₂ := eq1535
       grind)
    | exact superpose eq1535 eq181
    | (have r₁ := eq181
       have r₂ := eq1535
       grind)
    | exact resolve eq181 eq1535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq1547 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op (M.op x y) x) ∨ x = (k (M.op x y) x) := by
    first
    | (have i₁ := eq630
       have i₂ := eq1535
       grind)
    | exact superpose eq1535 eq630
    | (have r₁ := eq630
       have r₂ := eq1535
       grind)
    | exact resolve eq630 eq1535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq1548 : x = (k (M.op x y) x) ∨ x = (M.op (M.op x y) x) := by grind
  clear eq1547
  have eq1549 : (k x (M.op x y)) = (M.op (M.op x y) x) := by grind
  clear eq1546
  have eq1552 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1542 eq20
    | exact resolve eq20 eq1542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1542
  have eq1612 : (M.op x y) = (k x x) := by
    first
    | exact superpose eq1541 eq738
    | exact resolve eq738 eq1541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1541
  have eq1649 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq1612
       grind)
    | exact superpose eq1612 eq39
    | exact resolve eq39 eq1612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1660 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1649
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1649
    | exact resolve eq1649 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1649
  have eq1668 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq1660
    | exact resolve eq1660 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1660
  have eq1672 : (σ y) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1552 eq1668
    | exact resolve eq1668 eq1552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1668
  have eq1679 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1672 eq702
    | (have j0 := eq702 (σ x) (σ x)
       grind)
    | exact resolve eq702 eq1672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq1680 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1679
  have eq1695 : x ≠ (k x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1533
       grind)
    | exact superpose eq1533 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq1533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533
  have eq1706 : x ≠ (k x (M.op x y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1695
       have i₂ := eq1535
       grind)
    | exact superpose eq1535 eq1695
    | exact resolve eq1695 eq1535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695
  have eq1715 : (k (M.op x y) x) = (M.op x (M.op x y)) ∨ x ≠ (k x (M.op x y)) := by
    first
    | (have i₁ := eq1706
       have i₂ := eq1535
       grind)
    | exact superpose eq1535 eq1706
    | exact resolve eq1706 eq1535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535 eq1706
  have eq1723 : (k x x) = (k (M.op x y) x) ∨ x ≠ (k x (M.op x y)) := by
    first
    | exact superpose eq738 eq1715
    | exact resolve eq1715 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738 eq1715
  have eq1725 : x ≠ (k x (M.op x y)) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | (have i₁ := eq1723
       have i₂ := eq1612
       grind)
    | exact superpose eq1612 eq1723
    | exact resolve eq1723 eq1612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1612 eq1723
  have eq2803 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1548 eq1543
    | exact resolve eq1543 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543 eq1548
  have eq2817 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq2803
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2803
    | exact resolve eq2803 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2803
  have eq2820 : (σ x) = (k (σ y) (σ x)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq1549 eq2817
    | exact resolve eq2817 eq1549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1549 eq2817
  have eq2834 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq2820 eq736
    | (have j0 := eq736 (σ y) (σ x)
       grind)
    | (have r₁ := eq736 (σ y) (σ x)
       have r₂ := eq2820
       grind)
    | exact resolve eq736 eq2820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736 eq2820
  have eq2837 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x (M.op x y)) := by grind
  clear eq2834
  have eq2839 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq26 eq2837
    | exact resolve eq2837 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2837
  have eq2846 : x = (k x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq2839
    | exact resolve eq2839 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2839
  have eq3485 : x ≠ x ∨ (M.op x y) = (k (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2846 eq1725
    | (have r₁ := eq1725
       have r₂ := eq2846
       grind)
    | exact resolve eq1725 eq2846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1725
  have eq3495 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2846 eq1544
    | exact resolve eq1544 eq2846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544 eq2846
  have eq3502 : (M.op x y) = (k (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3485
  have eq3505 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3495
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3495
    | exact resolve eq3495 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3495
  have eq3692 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3502 eq39
    | exact resolve eq39 eq3502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq3502
  have eq3698 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq3692
    | exact resolve eq3692 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3692
  have eq3701 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1552 eq3698
    | exact resolve eq3698 eq1552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3698
  have eq3712 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3505 eq649
    | exact resolve eq649 eq3505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649 eq3505
  have eq3727 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3712
  have eq3857 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3727 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq3727
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq3727
       grind)
    | exact resolve eq13 eq3727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3727
  have eq3870 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3857
  have eq3879 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3870
    | exact resolve eq3870 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3870
  have eq3885 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3701 eq3879
    | exact resolve eq3879 eq3701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3701 eq3879
  have eq3886 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3885
  have eq3889 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3886 eq27
    | exact resolve eq27 eq3886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3886
  have eq3905 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq3889
       have r₂ := eq1552
       grind)
    | exact resolve eq3889 eq1552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3889
  have eq3910 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq3905 eq27
    | exact resolve eq27 eq3905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq3911 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq3905 eq175
    | exact resolve eq175 eq3905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq3921 : (σ x) ≠ (σ y) := by
    first
    | exact superpose eq1552 eq3910
    | exact resolve eq3910 eq1552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552 eq3910
  have eq3923 : ∀ X0 : G, (σ x) = (M.op (k (σ x) (σ x)) (M.op (σ y) X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq3911 X0
       have i₂ := eq11 sF2 sF2
       grind)
    | exact superpose eq11 eq3911
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq3911 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3911
  have eq3950 : ∀ X0 : G, (σ x) = (M.op (k (σ x) (σ x)) (M.op (σ y) X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq3923 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3923
  have eq3957 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq1672 eq3950
    | exact resolve eq3950 eq1672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3950
  have eq3959 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3957 x
       have i₂ := eq177 sF3 x
       grind)
    | exact superpose eq177 eq3957
    | exact resolve eq3957 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3957
  have eq4603 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq3959 eq198
    | exact resolve eq198 eq3959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq3959
  have eq4614 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq4603
    | (have j0 := eq4603 X0
       grind)
    | exact resolve eq4603 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4603
  have eq4624 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ x) X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq3905 eq4614
    | exact resolve eq4614 eq3905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4614
  have eq4630 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4624 x
       have i₂ := eq177 sF2 x
       grind)
    | exact superpose eq177 eq4624
    | exact resolve eq4624 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4624
  have eq4737 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4630 eq177
    | exact resolve eq177 eq4630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq4630
  have eq4754 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq4737
    | exact resolve eq4737 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4737
  have eq4762 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3905 eq4754
    | exact resolve eq4754 eq3905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3905 eq4754
  have eq4764 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq4762
       have r₂ := eq1680
       grind)
    | exact resolve eq4762 eq1680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1680 eq4762
  have eq4776 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq4764 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq4764
       grind)
    | exact resolve eq13 eq4764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4764
  have eq4791 : (σ x) = (k (σ x) (σ x)) := by grind
  clear eq4776
  have eq4869 : (σ x) = (σ y) := by
    first
    | exact superpose eq4791 eq1672
    | exact resolve eq1672 eq4791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672 eq4791
  have eq4889 : False := by grind
  exact eq4889

/-- `Equation2062`: `x = ((x ◇ y) ◇ y) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(Y,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxy_y_pyy_x_pxy_Equation2062 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2062 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2062.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X2)) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op (M.op x y) y) (M.op x X0)) := by
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
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 (M.op X0 X2)) (M.op (M.op (M.op X0 X1) X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X1) (M.op X0 X2) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 (M.op X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X1)) (M.op X0 X1) X2
       have i₂ := eq14 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, x = (M.op (M.op (M.op x X0) X0) (M.op x y)) := by
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
  have eq55 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) X0) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (M.op (M.op (M.op X0 X1) X1) X2) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X1) X2 (M.op X0 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) := by
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
  clear eq49
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
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq91
    | exact resolve eq91 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq100 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
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
  have eq240 : x = (M.op (M.op (M.op x y) y) (M.op x y)) := by
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
  have eq244 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op (M.op (M.op x y) y) X0) X0) x) := by
    intro X0
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq251 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq263 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x (M.op (M.op x (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0)) := by
    intro X0
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
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
  have eq301 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq290 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq290
    | exact resolve eq290 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq303 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq301 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq301
    | exact resolve eq301 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq301
  have eq682 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X1) X2) X2) = (M.op (M.op (M.op (M.op X0 X1) X1) X0) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 (M.op (M.op X0 X1) X1) X2 X0
       have i₂ := eq56 X0 X1 X2
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq683 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 (M.op X0 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X0 X1 (M.op X0 X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq684 : ∀ X0 : G, (M.op (M.op x X0) X0) = (M.op (M.op x (M.op x y)) x) := by
    intro X0
    first
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq685 : ∀ X0 : G, (M.op (M.op (σ x) X0) X0) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq687 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56 (M.op X0 X0) X0 X0
       have i₂ := eq56 X0 X0 X0
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq695 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq687 X0
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq687
    | exact resolve eq687 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq698 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X0 X1
       have i₂ := eq695 X0
       grind)
    | exact superpose eq695 eq14
    | exact resolve eq14 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq725 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq303 X0
       grind)
    | exact superpose eq303 eq16
    | exact resolve eq16 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq830 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X2)) = (M.op X0 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X2 (M.op (M.op (M.op X0 X1) X1) x)
       have i₂ := eq52 X0 X1 X2 x
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq53
  have eq1331 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq240 eq244
    | exact resolve eq244 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq1356 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | exact superpose eq684 eq1331
    | exact resolve eq1331 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq1359 : (M.op x (M.op x y)) = (M.op x (M.op (M.op x y) y)) := by
    first
    | exact superpose eq1331 eq263
    | exact resolve eq263 eq1331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263 eq1331
  have eq1384 : x = (M.op (M.op (M.op x y) y) x) := by
    first
    | (have i₁ := eq695 x
       have i₂ := eq1356 x
       grind)
    | exact superpose eq1356 eq695
    | exact resolve eq695 eq1356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1385 : (M.op x x) = (M.op x (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq698 x x
       have i₂ := eq1356 x
       grind)
    | exact superpose eq1356 eq698
    | exact resolve eq698 eq1356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1356
  have eq1415 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq251 eq255
    | exact resolve eq255 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq1458 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | exact superpose eq685 eq1415
    | exact resolve eq1415 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq1461 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq1415 eq270
    | exact resolve eq270 eq1415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq1415
  have eq1506 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by
    first
    | exact superpose eq1458 eq695
    | exact resolve eq695 eq1458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1507 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq1458 eq698
    | exact resolve eq698 eq1458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1458
  have eq1611 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) y) X0) X0) = (M.op (M.op (M.op (M.op x y) y) x) (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq240 eq683
    | exact resolve eq683 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq1618 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X0) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq251 eq683
    | exact resolve eq683 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq1635 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq683 X0 X1 x
       have i₂ := eq683 X0 X2 x
       grind)
    | exact superpose eq683 eq683
    | exact resolve eq683 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq1689 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X0) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq1506 eq1618
    | exact resolve eq1618 eq1506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1506 eq1618
  have eq1694 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) y) X0) X0) = (M.op x (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq1384 eq1611
    | exact resolve eq1611 eq1384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384 eq1611
  have eq1714 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X0) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1461 eq1689
    | exact resolve eq1689 eq1461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1689
  have eq1718 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op (M.op (M.op x y) y) X0) X0) := by
    intro X0
    first
    | exact superpose eq1359 eq1694
    | exact resolve eq1694 eq1359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1694
  have eq1730 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq1359 eq1385
    | exact resolve eq1385 eq1359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1359 eq1385
  have eq1758 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1461 eq1507
    | exact resolve eq1507 eq1461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1461 eq1507
  have eq1921 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq830 X0 X0 X1
       have i₂ := eq698 X0 X0
       grind)
    | exact superpose eq698 eq830
    | exact resolve eq830 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq2155 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1921 (σ X0) (σ X0)
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq1921
    | exact resolve eq1921 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq2158 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1921 (τ X0) (τ X0)
       have i₂ := eq725 X0
       grind)
    | exact superpose eq725 eq1921
    | exact resolve eq1921 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725 eq1921
  have eq2766 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1635 (M.op X0 X0) X0 X1
       have i₂ := eq695 X0
       grind)
    | exact superpose eq695 eq1635
    | exact resolve eq1635 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2844 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq695 X0
       have i₂ := eq1635 X0 X0 X1
       grind)
    | (have i₁ := eq695 X0
       have i₂ := eq1635 X0 X1 X0
       grind)
    | exact superpose eq1635 eq695
    | exact resolve eq695 eq1635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq2854 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq698 X0 X0
       have i₂ := eq1635 X0 X0 X1
       grind)
    | (have i₁ := eq698 X0 X0
       have i₂ := eq1635 X0 X1 X0
       grind)
    | exact superpose eq1635 eq698
    | exact resolve eq698 eq1635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3999 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq1758 eq1714
    | exact resolve eq1714 eq1758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1714 eq1758
  have eq4000 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) y) X0) X0) := by
    intro X0
    first
    | exact superpose eq1730 eq1718
    | exact resolve eq1718 eq1730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1718 eq1730
  have eq4869 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3999 sF3
       have i₂ := eq1635 sF4 sF3 x
       grind)
    | (have i₁ := eq3999 sF3
       have i₂ := eq1635 sF4 x sF3
       grind)
    | exact superpose eq1635 eq3999
    | exact resolve eq3999 eq1635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4953 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) X0) X0) y) := by
    intro X0
    first
    | (have i₁ := eq4000 y
       have i₂ := eq1635 sF0 y x
       grind)
    | (have i₁ := eq4000 y
       have i₂ := eq1635 sF0 x y
       grind)
    | exact superpose eq1635 eq4000
    | exact resolve eq4000 eq1635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1635
  have eq6439 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X1) X2) X2) = (M.op X0 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq682 X0 X1 X2
       have i₂ := eq2844 X0 X1
       grind)
    | exact superpose eq2844 eq682
    | exact resolve eq682 eq2844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq6440 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X1) X2) X2) = (M.op X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6439 X0 X1 X2
       have i₂ := eq2854 X0 X1
       grind)
    | exact superpose eq2854 eq6439
    | exact resolve eq6439 eq2854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2854 eq6439
  have eq6547 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq3999 eq6440
    | exact resolve eq6440 eq3999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3999
  have eq6548 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) y) := by
    first
    | exact superpose eq4000 eq6440
    | exact resolve eq6440 eq4000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4000 eq6440
  have eq6861 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq6547 eq2766
    | exact resolve eq2766 eq6547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6547
  have eq6910 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq6861 eq698
    | exact resolve eq698 eq6861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6963 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq6910 eq6861
    | exact resolve eq6861 eq6910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6861 eq6910
  have eq7051 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq2766 x y
       have i₂ := eq6548
       grind)
    | exact superpose eq6548 eq2766
    | exact resolve eq2766 eq6548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2766 eq6548
  have eq7100 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq7051 eq698
    | exact resolve eq698 eq7051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq7154 : x = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq7100 eq7051
    | exact resolve eq7051 eq7100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7051 eq7100
  have eq47338 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq47339 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq47338
    | exact resolve eq47338 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47338
  have eq47350 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq47339
       have r₂ := eq27
       grind)
    | exact resolve eq47339 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47339
  have eq47354 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq47350
    | exact resolve eq47350 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47350
  have eq47358 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq47354
    | exact resolve eq47354 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47354
  have eq47382 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq47358 eq2844
    | exact resolve eq2844 eq47358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47358
  have eq47414 : (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6963 eq47382
    | exact resolve eq47382 eq6963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6963 eq47382
  have eq47451 : y = (M.op (M.op (M.op x y) x) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2844 y x
       have i₂ := eq47414
       grind)
    | exact superpose eq47414 eq2844
    | exact resolve eq2844 eq47414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47414
  have eq47483 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq7154 eq47451
    | exact resolve eq47451 eq7154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7154 eq47451
  have eq47521 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ y) X0) X0) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq47483 eq4869
    | exact resolve eq4869 eq47483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4869 eq47483
  have eq47580 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq47521 x
       have i₂ := eq2844 sF3 x
       grind)
    | exact superpose eq2844 eq47521
    | exact resolve eq47521 eq2844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47521
  have eq47900 : (τ (σ y)) = (M.op (τ (σ x)) (τ (σ y))) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq47580 eq2158
    | exact resolve eq2158 eq47580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2158 eq47580
  have eq47994 : y = (M.op (τ (σ x)) y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29 eq47900
    | exact resolve eq47900 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47900
  have eq48016 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq28 eq47994
    | exact resolve eq47994 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47994
  have eq48021 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq48016
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq48016
    | exact resolve eq48016 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48016
  have eq48022 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq48021
  have eq48148 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq48022 eq29
    | exact resolve eq29 eq48022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq48022
  have eq48300 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq48148
    | exact resolve eq48148 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq48148
  have eq48301 : y = (M.op x y) ∨ x = y := by grind
  clear eq48300
  have eq48319 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq48301 eq20
    | exact resolve eq20 eq48301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48384 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op y X0) X0) y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq48301 eq4953
    | exact resolve eq4953 eq48301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4953 eq48301
  have eq48447 : y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq48384 x
       have i₂ := eq2844 y x
       grind)
    | exact superpose eq2844 eq48384
    | exact resolve eq48384 eq2844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2844 eq48384
  have eq48504 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq48319
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48319
    | exact resolve eq48319 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48319
  have eq48851 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2155 x
       have i₂ := eq48447
       grind)
    | exact superpose eq48447 eq2155
    | exact resolve eq2155 eq48447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2155 eq48447
  have eq48948 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq48851
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48851
    | exact resolve eq48851 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48851
  have eq48972 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq48948
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq48948
    | exact resolve eq48948 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48948
  have eq48979 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq48972
    | exact resolve eq48972 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48972
  have eq48982 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq48979 eq27
    | exact resolve eq27 eq48979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48979
  have eq49075 : x = y := by
    first
    | (have r₁ := eq48982
       have r₂ := eq48504
       grind)
    | exact resolve eq48982 eq48504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48504 eq48982
  have eq49080 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq49075
       grind)
    | exact superpose eq49075 eq18
    | exact resolve eq18 eq49075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq49081 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq49075
       grind)
    | exact superpose eq49075 eq24
    | exact resolve eq24 eq49075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq49075
  have eq49237 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq49081
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq49081
    | exact resolve eq49081 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq49081
  have eq49257 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq49237 eq26
    | exact resolve eq26 eq49237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq49237
  have eq49701 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq49257 eq73
    | exact resolve eq73 eq49257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq49257
  have eq49868 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq49701
       have i₂ := eq49080
       grind)
    | exact superpose eq49080 eq49701
    | exact resolve eq49701 eq49080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49080 eq49701
  have eq49935 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq49868 eq15
    | exact resolve eq15 eq49868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49868
  have eq49986 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq49935
    | exact resolve eq49935 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq49935
  have eq49999 : False := by grind
  exact eq49999

/-- `Equation2062`: `x = ((x ◇ y) ◇ y) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = m(X,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pxy_pxy_x_pxy_Equation2062 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2062 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2062.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X2)) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op (M.op x y) y) (M.op x X0)) := by
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
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 (M.op X0 X2)) (M.op (M.op (M.op X0 X1) X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X1) (M.op X0 X2) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 (M.op X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X1)) (M.op X0 X1) X2
       have i₂ := eq14 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, x = (M.op (M.op (M.op x X0) X0) (M.op x y)) := by
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
  have eq55 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) X0) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (M.op (M.op (M.op X0 X1) X1) X2) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X1) X2 (M.op X0 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op y x) ∨ x = (k x y) := by
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
  have eq79 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 (M.op X1 X1)
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq97 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq97
    | (have j0 := eq97 (σ X0) (σ X1)
       grind)
    | exact resolve eq97 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq97 x y
       grind)
    | exact superpose eq97 eq44
    | (have j1 := eq97 x y
       grind)
    | exact resolve eq44 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
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
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq116
    | exact resolve eq116 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq118
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq118
    | exact resolve eq118 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq127 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq135 : (σ (k x (k (M.op x y) x))) = (k (σ x) (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq127 eq35
    | exact resolve eq35 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq184 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq97 (σ X0) sF3
       grind)
    | exact superpose eq97 eq40
    | (have j1 := eq97 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq202 : x = (M.op (M.op (M.op x y) y) (M.op x y)) := by
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
  have eq205 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op (M.op (M.op x y) y) X0) X0) x) := by
    intro X0
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x (M.op (M.op x (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0)) := by
    intro X0
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X0) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) X0) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348 : ∀ X0 X1 : G, (σ (k x (k X0 (τ X1)))) = (k (σ x) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq35
    | exact resolve eq35 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq353 : ∀ X0 X1 : G, (σ (k (k X0 (τ X1)) (M.op x y))) = (k (k (σ X0) X1) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq41 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq41
    | exact resolve eq41 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq473 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 X1) X1) X0) = (M.op (M.op (M.op X0 X1) X1) (M.op (M.op (M.op (M.op X0 X1) X1) X0) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq53 (M.op (M.op X0 X1) X1) (M.op X0 x) x
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq474 : ∀ X1 : G, (M.op (M.op (M.op x y) y) x) = (M.op (M.op (M.op x y) y) (M.op (M.op (M.op (M.op x y) y) x) X1)) := by
    intro X1
    first
    | exact superpose eq50 eq53
    | exact resolve eq53 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq475 : ∀ X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) X1)) := by
    intro X1
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X0 (M.op X0 X1)) X2)) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X0 (M.op X0 X1)) X2) X3
       have i₂ := eq53 X0 X1 X2
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq598 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq119 eq97
    | (have j0 := eq97 (σ x) (σ y)
       grind)
    | exact resolve eq97 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq599 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq598
    | exact resolve eq598 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq602 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq599
       have r₂ := eq27
       grind)
    | exact resolve eq599 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq604 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq602
    | exact resolve eq602 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq615 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq604 eq79
    | (have r₁ := eq79
       have r₂ := eq604
       grind)
    | exact resolve eq79 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq604
  have eq616 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq615
  have eq623 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X2)) = (M.op (M.op (M.op (M.op X0 (M.op X0 X2)) X3) X3) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 (M.op (M.op X0 X1) X1) (M.op X0 X2) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq638 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X1) X2) X2) = (M.op (M.op (M.op (M.op X0 X1) X1) X0) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 (M.op (M.op X0 X1) X1) X2 X0
       have i₂ := eq56 X0 X1 X2
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq639 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 (M.op X0 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X0 X1 (M.op X0 X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq640 : ∀ X0 : G, (M.op (M.op x X0) X0) = (M.op (M.op x (M.op x y)) x) := by
    intro X0
    first
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq641 : ∀ X0 : G, (M.op (M.op (σ x) X0) X0) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq643 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56 (M.op X0 X0) X0 X0
       have i₂ := eq56 X0 X0 X0
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq649 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq643 X0
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq643
    | exact resolve eq643 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq671 : ∀ X0 X2 : G, (M.op (M.op (M.op (M.op x y) y) X0) X0) = (M.op (M.op (M.op (M.op x y) y) x) (M.op (M.op (M.op (M.op (M.op x y) y) X0) X0) X2)) := by
    intro X0 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq672 : ∀ X0 X2 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X0) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X0) X2)) := by
    intro X0 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq684 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op (M.op X0 X1) X1) X3)) = (M.op (M.op (M.op X0 (M.op X0 X2)) (M.op (M.op X0 (M.op X0 X2)) X4)) (M.op (M.op (M.op (M.op X0 X1) X1) (M.op (M.op (M.op X0 X1) X1) X3)) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 (M.op X0 (M.op X0 X2)) (M.op (M.op (M.op X0 X1) X1) X3) X2 X3
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (M.op (M.op (M.op X0 X1) X1) X0) (M.op (M.op (M.op (M.op X0 X1) X1) X0) X2)) (M.op (M.op (M.op X0 X1) X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 (M.op (M.op (M.op X0 X1) X1) X0) X0 X2 X3
       have i₂ := eq56 X0 X1 X0
       grind)
    | exact superpose eq56 eq52
    | exact resolve eq52 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq706 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X2)) = (M.op X0 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X2 (M.op (M.op (M.op X0 X1) X1) x)
       have i₂ := eq52 X0 X1 X2 x
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq729 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq616 eq119
    | exact resolve eq119 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq730 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq616 eq60
    | exact resolve eq60 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq616
  have eq732 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq729
  have eq735 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq28 eq730
    | exact resolve eq730 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq776 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq101 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X0)
       have i₂ := eq101 X0 X1
       grind)
    | exact superpose eq101 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq101 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq101 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq101 X1 X1
       grind)
    | exact resolve eq12 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq793 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq101 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq795 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq776 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq799 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq795 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq795
    | (have j0 := eq795 X0 X1
       grind)
    | exact resolve eq795 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq814 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq732 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq732
       grind)
    | exact resolve eq13 eq732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq821 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq814
  have eq822 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq821
    | exact resolve eq821 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq827 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq822 eq119
    | exact resolve eq119 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq830 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq827
  have eq834 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq830
       have r₂ := eq27
       grind)
    | exact resolve eq830 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq837 : x = (M.op (M.op (M.op x y) x) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq834
       grind)
    | exact superpose eq834 eq54
    | exact resolve eq54 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq948 : x = (M.op (M.op (M.op x y) x) x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq649 x
       have i₂ := eq834
       grind)
    | exact superpose eq834 eq649
    | exact resolve eq649 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq954 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X0 X1
       have i₂ := eq649 X0
       grind)
    | exact superpose eq649 eq14
    | exact resolve eq14 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq956 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 (M.op (M.op X0 X0) X0)) = (k X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op (M.op X0 X0) X0)
       have i₂ := eq649 X0
       grind)
    | exact superpose eq649 eq13
    | (have j0 := eq13 X0 (M.op (M.op X0 X0) X0)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq649 X0
       grind)
    | exact resolve eq13 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq965 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (k X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq956 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq972 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op x y) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq948 eq14
    | exact resolve eq14 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq986 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq972 eq54
    | exact resolve eq54 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1046 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x y) (M.op (M.op x y) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq986 eq53
    | exact resolve eq53 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1166 : ∀ X0 : G, (M.op (M.op x (M.op x y)) x) = (M.op (M.op x y) (M.op (M.op x y) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq972 eq640
    | exact resolve eq640 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1175 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op x (M.op (M.op x (M.op x y)) x)) := by
    intro X0
    first
    | (have i₁ := eq53 x X0 (M.op x X0)
       have i₂ := eq640 (M.op x X0)
       grind)
    | exact superpose eq640 eq53
    | exact resolve eq53 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1178 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x (M.op x y)) x) X0) (M.op (M.op x X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op x X0) X0 X1
       have i₂ := eq640 X0
       grind)
    | exact superpose eq640 eq14
    | exact resolve eq14 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1179 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x X0) X1) X1) (M.op (M.op x (M.op x y)) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op x X0) X1 X0
       have i₂ := eq640 X0
       grind)
    | exact superpose eq640 eq14
    | exact resolve eq14 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1186 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x (M.op (M.op x X0) X0)) := by
    intro X0
    first
    | exact superpose eq640 eq219
    | exact resolve eq219 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1196 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq219 eq1175
    | exact resolve eq1175 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175
  have eq1197 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = (M.op (M.op x y) (M.op (M.op x y) X1)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq1166 eq1166
    | exact resolve eq1166 eq1166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1198 : ∀ X0 X1 : G, (M.op (M.op x X0) X0) = (M.op (M.op x y) (M.op (M.op x y) X1)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq640 eq1166
    | exact resolve eq1166 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1216 : (M.op (M.op x y) x) = (M.op (M.op x (M.op x y)) x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1166 eq1046
    | exact resolve eq1046 eq1166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1221 : (M.op x y) = (M.op x (M.op (M.op x (M.op x y)) x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1166 eq972
    | exact resolve eq972 eq1166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972
  have eq1234 : (M.op x y) = (M.op x (M.op (M.op x (M.op x y)) x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1221
  have eq1239 : (M.op (M.op x y) x) = (M.op (M.op x (M.op x y)) x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1216
  have eq1245 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = (M.op (M.op x y) (M.op (M.op x y) X1)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | (have j0 := eq1197 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197
  have eq1246 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq219 eq1234
    | exact resolve eq1234 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234
  have eq1256 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) x) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1246 eq13
    | (have j0 := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq1246
       grind)
    | exact resolve eq13 eq1246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1265 : (k (M.op x y) x) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1256
  have eq1292 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0)) := by
    intro X0
    first
    | exact superpose eq224 eq641
    | exact resolve eq641 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq1304 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (M.op (σ x) X0) X1) X1) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq641 eq14
    | exact resolve eq14 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1355 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq202 eq205
    | exact resolve eq205 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq1405 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq207 eq210
    | exact resolve eq210 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq1595 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq649 x
       have i₂ := eq1198 x X0
       grind)
    | exact superpose eq1198 eq649
    | exact resolve eq649 eq1198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198
  have eq1720 : x = (M.op (M.op (M.op x (M.op x y)) x) x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1166 eq1595
    | exact resolve eq1595 eq1166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166 eq1595
  have eq1734 : x = (M.op (M.op (M.op x (M.op x y)) x) x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1720
  have eq1773 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) X1) X1) = (M.op (M.op (M.op (M.op X0 X0) X0) X0) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq639 (M.op (M.op X0 X0) X0) X1 X0
       have i₂ := eq649 X0
       grind)
    | exact superpose eq649 eq639
    | exact resolve eq639 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1835 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq639 X0 X1 x
       have i₂ := eq639 X0 X2 x
       grind)
    | exact superpose eq639 eq639
    | exact resolve eq639 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1836 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq986 eq639
    | exact resolve eq639 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq1853 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 (M.op X0 X1)) X0) X2) (M.op (M.op X0 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X2) X2 X3
       have i₂ := eq639 X0 X2 X1
       grind)
    | exact superpose eq639 eq14
    | exact resolve eq14 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1854 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 X2) X3) X3) (M.op (M.op X0 (M.op X0 X1)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X2) X3 X2
       have i₂ := eq639 X0 X2 X1
       grind)
    | exact superpose eq639 eq14
    | exact resolve eq14 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1884 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1773 X0 X1
       have i₂ := eq14 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq14 eq1773
    | exact resolve eq1773 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1773
  have eq1888 : ∀ X0 : G, x = (M.op (M.op (M.op x y) x) (M.op (M.op x y) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1046 eq1836
    | exact resolve eq1836 eq1046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046
  have eq1915 : ∀ X0 : G, x = (M.op (M.op (M.op x y) x) (M.op (M.op x y) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq1888 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1888
  have eq2151 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op (M.op X0 X1) X1) X2)) = (M.op (M.op (M.op X0 X1) X1) (M.op X0 (M.op X0 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq706 (M.op (M.op X0 X1) X1) (M.op X0 X3) X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq706
    | exact resolve eq706 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2168 : ∀ X0 : G, (M.op (M.op (M.op x y) y) (M.op (M.op (M.op x y) y) X0)) = (M.op (M.op (M.op x y) y) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq202 eq706
    | exact resolve eq706 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq2176 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq207 eq706
    | exact resolve eq706 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq2234 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 (M.op (M.op X0 X1) X1)) ∨ (M.op (M.op X0 X2) X0) = X0 ∨ (k X0 (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X0 X2)
       have i₂ := eq706 X0 X1 X2
       grind)
    | exact superpose eq706 eq12
    | (have j0 := eq12 X0 (M.op X0 X2)
       grind)
    | exact resolve eq12 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2244 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X0 X3)) X0) = (M.op (M.op X0 (M.op (M.op X0 X1) X1)) (M.op X0 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq639 X0 (M.op X0 X2) X3
       have i₂ := eq706 X0 X1 X2
       grind)
    | exact superpose eq706 eq639
    | exact resolve eq639 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2293 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op (M.op X0 X2) X2) ∨ (M.op (M.op (M.op X0 X2) X2) X0) = (k (M.op (M.op X0 X2) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X0 X2) X2) X0
       have i₂ := eq706 X0 X2 X1
       grind)
    | exact superpose eq706 eq13
    | (have j0 := eq13 (M.op (M.op X0 X2) X2) X0
       grind)
    | (have r₁ := eq13 (M.op X0 (M.op (M.op X0 X1) X1)) X0
       have r₂ := eq706 X0 X1 (M.op (M.op X0 X1) X1)
       grind)
    | exact resolve eq13 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2350 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq51 eq2176
    | exact resolve eq2176 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2176
  have eq2353 : ∀ X0 : G, x = (M.op (M.op (M.op x y) y) (M.op (M.op (M.op x y) y) X0)) := by
    intro X0
    first
    | exact superpose eq50 eq2168
    | exact resolve eq2168 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq2168
  have eq2359 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op (M.op X0 X1) X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2151 X0 X1 X2 x
       have i₂ := eq14 X0 X1 (M.op X0 x)
       grind)
    | exact superpose eq14 eq2151
    | exact resolve eq2151 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2151
  have eq3044 : x ≠ x ∨ (M.op x (M.op (M.op x (M.op x y)) x)) = (k x (M.op (M.op x (M.op x y)) x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1734 eq13
    | (have j0 := eq13 x (M.op (M.op x (M.op x y)) x)
       grind)
    | (have r₁ := eq13 x (M.op (M.op x (M.op x y)) x)
       have r₂ := eq1734
       grind)
    | exact resolve eq13 eq1734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734
  have eq3055 : (M.op x (M.op (M.op x (M.op x y)) x)) = (k x (M.op (M.op x (M.op x y)) x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3044
  have eq3061 : (M.op x (M.op x y)) = (k x (M.op (M.op x (M.op x y)) x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq219 eq3055
    | exact resolve eq3055 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq3055
  have eq5898 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op (M.op x y) X1)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq1245 eq1836
    | exact resolve eq1836 eq1245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1245 eq1836
  have eq5923 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op (M.op x y) X1)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | (have j0 := eq5898 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5898
  have eq7318 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (σ x) (σ y))) X1)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) X0) X0) (M.op (M.op (M.op (σ x) X0) X0) X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq227 eq706
    | exact resolve eq706 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7320 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X0) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (σ x) (σ y))) X1)) := by
    intro X0 X1
    first
    | exact superpose eq227 eq7318
    | exact resolve eq7318 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq7318
  have eq7434 : ∀ X0 : G, (M.op (M.op (M.op x y) y) x) = (M.op (M.op (M.op x y) y) (M.op (M.op (M.op x y) y) X0)) := by
    intro X0
    first
    | (have i₁ := eq474 x
       have i₂ := eq706 (M.op sF0 y) x x
       grind)
    | exact superpose eq706 eq474
    | exact resolve eq474 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq7545 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq475 sF2
       have i₂ := eq706 (M.op sF4 sF3) sF2 x
       grind)
    | exact superpose eq706 eq475
    | exact resolve eq475 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq11553 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq184 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq184
    | (have j0 := eq184 x
       grind)
    | exact resolve eq184 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq11580 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | exact superpose eq26 eq11553
    | exact resolve eq11553 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11553
  have eq11587 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11580
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq11580
    | exact resolve eq11580 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11580
  have eq11592 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11587
    | exact resolve eq11587 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11587
  have eq12202 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X0 X1)) X2) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq486 X0 X1 x (M.op X0 X1)
       have i₂ := eq639 (M.op X0 (M.op X0 X1)) X2 x
       grind)
    | exact superpose eq639 eq486
    | exact resolve eq486 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13958 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (k (τ X0) X1)) ∨ (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq793 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq793
    | exact resolve eq793 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13985 : ∀ X0 : G, (σ (k x X0)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq793 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq793
    | (have j0 := eq793 x X0
       grind)
    | exact resolve eq793 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793
  have eq13996 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13958 X0 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq13958
    | (have j0 := eq13958 X0 X1
       grind)
    | exact resolve eq13958 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13958
  have eq14015 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13996 X0 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq13996
    | (have j0 := eq13996 X0 X1
       grind)
    | exact resolve eq13996 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13996
  have eq14372 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X2)) = (M.op (M.op (M.op (M.op X0 X1) X1) X0) (M.op (M.op X0 X3) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq623 X0 X3 X2 X0
       have i₂ := eq639 X0 X1 X2
       grind)
    | exact superpose eq639 eq623
    | exact resolve eq623 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623 eq639
  have eq15189 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X0) = (M.op (M.op (M.op X0 X1) X1) (M.op (M.op (M.op X0 X1) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq473 X0 X1 X0
       have i₂ := eq706 (M.op (M.op X0 X1) X1) X0 X2
       grind)
    | exact superpose eq706 eq473
    | exact resolve eq473 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq15524 : ∀ X1 : G, (M.op (M.op (M.op (M.op x (M.op x y)) x) X1) X1) = (M.op (M.op (M.op (M.op x (M.op x y)) x) x) (M.op (M.op x (M.op x y)) x)) := by
    intro X1
    first
    | (have i₁ := eq638 x x x
       have i₂ := eq640 x
       grind)
    | exact superpose eq640 eq638
    | exact resolve eq638 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq15539 : ∀ X1 : G, (M.op (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) X1) X1) = (M.op (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) (σ x)) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x))) := by
    intro X1
    first
    | exact superpose eq641 eq638
    | exact resolve eq638 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638 eq641
  have eq15627 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) X1) X1) := by
    intro X1
    first
    | (have i₁ := eq15539 X1
       have i₂ := eq14 (M.op sF2 sF4) sF2 sF2
       grind)
    | exact superpose eq14 eq15539
    | exact resolve eq15539 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15539
  have eq15631 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op (M.op (M.op (M.op x (M.op x y)) x) X1) X1) := by
    intro X1
    first
    | (have i₁ := eq15524 X1
       have i₂ := eq14 (M.op x sF0) x x
       grind)
    | exact superpose eq14 eq15524
    | exact resolve eq15524 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15524
  have eq15651 : (M.op x y) = (k x (M.op (M.op x y) x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1246 eq3061
    | exact resolve eq3061 eq1246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246
  have eq15655 : (M.op x (M.op x y)) = (k x (M.op (M.op x y) x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1239 eq3061
    | exact resolve eq3061 eq1239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239 eq3061
  have eq15662 : (M.op x (M.op x y)) = (k x (M.op (M.op x y) x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq15655
  have eq15666 : (M.op x y) = (k x (M.op (M.op x y) x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq15651
  have eq15763 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op x y) y) x) (M.op (M.op (M.op (M.op x y) y) x) X1)) = (M.op (M.op (M.op (M.op x y) y) x) (M.op (M.op (M.op (M.op (M.op x y) y) X0) X0) (M.op (M.op (M.op (M.op (M.op x y) y) X0) X0) X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq671 eq706
    | exact resolve eq706 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15765 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) y) X0) X0) = (M.op (M.op (M.op (M.op x y) y) x) (M.op (M.op (M.op (M.op x y) y) x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq671 eq15763
    | exact resolve eq15763 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671 eq15763
  have eq16156 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X0) (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X0) X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq672 eq706
    | exact resolve eq706 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq16158 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X0) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq672 eq16156
    | exact resolve eq16156 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672 eq16156
  have eq17748 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq799 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq799
    | exact resolve eq799 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17781 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (k X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq799 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq799
    | (have j0 := eq799 X1 (τ X0)
       grind)
    | exact resolve eq799 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799
  have eq17853 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (k X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17781 X0 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq17781
    | (have j0 := eq17781 X0 X1
       grind)
    | exact resolve eq17781 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17781
  have eq17857 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17748 X0 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq17748
    | (have j0 := eq17748 X0 X1
       grind)
    | exact resolve eq17748 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17748
  have eq17861 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (k X1 (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq17853 X0 X1
       have j1 := eq13 (σ X1) X0
       grind)
    | (have r₁ := eq17853 X1 X1
       have r₂ := eq13 (σ X1) X1
       grind)
    | exact resolve eq17853 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17853
  have eq17865 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq17857 X0 X1
       have j1 := eq13 X0 (σ X1)
       grind)
    | (have r₁ := eq17857 X0 X1
       have r₂ := eq13 X0 (σ X1)
       grind)
    | exact resolve eq17857 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17857
  have eq17869 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17861 X0 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq17861
    | (have j0 := eq17861 X0 X1
       grind)
    | exact resolve eq17861 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq17861
  have eq17873 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17865 X0 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq17865
    | (have j0 := eq17865 X0 X1
       grind)
    | exact resolve eq17865 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq17865
  have eq35467 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) X0) X0) (M.op (M.op (M.op (M.op X0 X0) X0) X0) X1)) = (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) X2)) (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) X2)) X3)) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq684 (M.op X0 X0) X0 X2 X1 X3 (M.op (M.op (M.op X0 X0) X0) x)
       have i₂ := eq697 X0 X0 X1 x
       grind)
    | exact superpose eq697 eq684
    | exact resolve eq684 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684 eq697
  have eq35538 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) X0) (M.op (M.op (M.op (M.op X0 X0) X0) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35467 X0 X1 x x
       have i₂ := eq486 (M.op X0 X0) x x X0
       grind)
    | exact superpose eq486 eq35467
    | exact resolve eq35467 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486 eq35467
  have eq35559 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35538 X0 X1
       have i₂ := eq649 X0
       grind)
    | exact superpose eq649 eq35538
    | exact resolve eq35538 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649 eq35538
  have eq56264 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op (M.op (M.op x y) x) X0) X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq837 eq1835
    | exact resolve eq1835 eq837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837 eq1835
  have eq60799 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x (M.op (M.op x y) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1915 eq56264
    | exact resolve eq56264 eq1915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1915 eq56264
  have eq60954 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x (M.op (M.op x y) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq60799 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60799
  have eq62272 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq2350 x
       have i₂ := eq35559 (M.op sF4 sF3) x
       grind)
    | exact superpose eq35559 eq2350
    | exact resolve eq2350 eq35559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2350
  have eq63175 : x = (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq2353 x
       have i₂ := eq35559 (M.op sF0 y) x
       grind)
    | exact superpose eq35559 eq2353
    | exact resolve eq2353 eq35559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2353
  have eq69733 : ∀ X0 X2 : G, (M.op (M.op (M.op X0 X0) X2) X2) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq12202 X0 x X2
       have i₂ := eq35559 X0 x
       grind)
    | exact superpose eq35559 eq12202
    | exact resolve eq12202 eq35559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12202
  have eq78908 : (k (σ x) (k (σ (M.op x y)) (σ x))) = (σ (k x (M.op (M.op x y) x))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1265 eq135
    | exact resolve eq135 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq1265
  have eq99730 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) X1) := by
    intro X1
    first
    | exact superpose eq1405 eq15627
    | exact resolve eq15627 eq1405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15627
  have eq100731 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op (M.op (M.op (M.op x y) y) X1) X1) := by
    intro X1
    first
    | exact superpose eq1355 eq15631
    | exact resolve eq15631 eq1355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15631
  have eq104641 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq735 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq735
       grind)
    | exact resolve eq13 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq104689 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq104641
  have eq104719 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq104689
    | exact resolve eq104689 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104689
  have eq106070 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (k x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq104719 eq119
    | exact resolve eq119 eq104719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq104719
  have eq106075 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (k x y) := by grind
  clear eq106070
  have eq106078 : (M.op x y) = (M.op x x) ∨ x = (k x y) := by
    first
    | (have r₁ := eq106075
       have r₂ := eq27
       grind)
    | exact resolve eq106075 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106075
  have eq106287 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y x) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq106078
       grind)
    | exact superpose eq106078 eq78
    | (have r₁ := eq78
       have r₂ := eq106078
       grind)
    | exact resolve eq78 eq106078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq106078
  have eq106511 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y x) ∨ x = (k x y) := by grind
  clear eq106287
  have eq106512 : x = (k x y) ∨ x = (M.op y x) := by grind
  clear eq106511
  have eq107068 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq106512
       grind)
    | exact superpose eq106512 eq44
    | exact resolve eq44 eq106512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106512
  have eq107087 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq107068
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq107068
    | exact resolve eq107068 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107068
  have eq107093 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11592 eq107087
    | exact resolve eq107087 eq11592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107087
  have eq117091 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq965 X0
       have i₂ := eq954 X0 X0
       grind)
    | exact superpose eq954 eq965
    | exact resolve eq965 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965
  have eq117318 : ∀ X0 : G, x = (k (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op x (M.op (M.op x y) (M.op (M.op x y) X0)))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq5923 eq117091
    | exact resolve eq117091 eq5923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5923
  have eq117478 : x = (k (M.op (M.op x y) (M.op x y)) (M.op x (M.op (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq117318 x
       have i₂ := eq35559 sF0 x
       grind)
    | exact superpose eq35559 eq117318
    | exact resolve eq117318 eq35559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117318
  have eq118039 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1292 x
       have i₂ := eq35559 (M.op sF2 sF4) x
       grind)
    | exact superpose eq35559 eq1292
    | exact resolve eq1292 eq35559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292
  have eq118040 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1405 eq118039
    | exact resolve eq118039 eq1405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118039
  have eq130200 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2359 X0 X1 x
       have i₂ := eq35559 (M.op (M.op X0 X1) X1) x
       grind)
    | exact superpose eq35559 eq2359
    | exact resolve eq2359 eq35559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2359
  have eq135381 : x = (k (M.op (M.op x y) (M.op x y)) (M.op x (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq60954 eq117478
    | exact resolve eq117478 eq60954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60954 eq117478
  have eq135391 : x = (k (M.op (M.op x y) (M.op x y)) (M.op x (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq135381
  have eq135407 : ∀ X0 : G, (M.op (M.op (σ x) X0) X0) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq7320 X0 x
       have i₂ := eq35559 (M.op sF2 sF4) x
       grind)
    | exact superpose eq35559 eq7320
    | exact resolve eq7320 eq35559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7320
  have eq135408 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | exact superpose eq118040 eq135407
    | exact resolve eq135407 eq118040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118040 eq135407
  have eq135975 : (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = (M.op (M.op (M.op x y) y) x) := by
    first
    | (have i₁ := eq7434 x
       have i₂ := eq35559 (M.op sF0 y) x
       grind)
    | exact superpose eq35559 eq7434
    | exact resolve eq7434 eq35559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7434
  have eq135976 : x = (M.op (M.op (M.op x y) y) x) := by
    first
    | exact superpose eq63175 eq135975
    | exact resolve eq135975 eq63175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63175 eq135975
  have eq136457 : (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq7545 x
       have i₂ := eq35559 (M.op sF4 sF3) x
       grind)
    | exact superpose eq35559 eq7545
    | exact resolve eq7545 eq35559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7545
  have eq136458 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by
    first
    | exact superpose eq62272 eq136457
    | exact resolve eq136457 eq62272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62272 eq136457
  have eq148417 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) y) X0) (M.op (M.op x X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1355 eq1178
    | exact resolve eq1178 eq1355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq149539 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x X0) X1) X1) (M.op (M.op x y) y)) := by
    intro X0 X1
    first
    | exact superpose eq1355 eq1179
    | exact resolve eq1179 eq1355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179 eq1355
  have eq152142 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (M.op (σ x) X0) X1) X1) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq1405 eq1304
    | exact resolve eq1304 eq1405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304 eq1405
  have eq163799 : (σ (M.op x (M.op x y))) = (k (σ x) (k (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq15662 eq78908
    | exact resolve eq78908 eq15662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15662
  have eq163800 : (σ (M.op x y)) = (k (σ x) (k (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq15666 eq78908
    | exact resolve eq78908 eq15666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15666 eq78908
  have eq163912 : (σ (M.op x y)) = (k (σ x) (k (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq163800
  have eq163913 : (σ (M.op x (M.op x y))) = (k (σ x) (k (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq163799
  have eq163927 : (σ (M.op x y)) = (k (σ x) (k (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq163912
    | exact resolve eq163912 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163912
  have eq163976 : (σ (M.op x y)) = (σ (M.op x (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq163913 eq163927
    | exact resolve eq163927 eq163913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163913
  have eq163981 : (σ (M.op x y)) = (σ (M.op x (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq163976
  have eq163994 : ∀ X0 : G, (k (σ X0) (σ (M.op x y))) = (σ (k X0 (M.op x (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq163981 eq10
    | exact resolve eq10 eq163981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164085 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq163981 eq17869
    | (have j0 := eq17869 X0 (M.op x y)
       grind)
    | exact resolve eq17869 eq163981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163981
  have eq164098 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (σ (k X0 (M.op x (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq41 eq163994
    | exact resolve eq163994 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq163994
  have eq167723 : (σ x) = (σ (k (M.op (M.op x y) (M.op x y)) (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq135391 eq164098
    | exact resolve eq164098 eq135391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135391 eq164098
  have eq167863 : (σ x) = (σ (k (M.op (M.op x y) (M.op x y)) (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq167723
  have eq167935 : (σ x) = (σ (k (M.op (M.op x y) (M.op x y)) (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq167863
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq167863
    | exact resolve eq167863 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167863
  have eq168054 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (k (σ x) X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq167935 eq17869
    | (have j0 := eq17869 X0 x
       grind)
    | exact resolve eq17869 eq167935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17869 eq167935
  have eq230552 : (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq164085 eq163927
    | (have j1 := eq164085 (σ x)
       grind)
    | exact resolve eq163927 eq164085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164085
  have eq230622 : (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by grind
  clear eq230552
  have eq243666 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq230622 eq168054
    | exact resolve eq168054 eq230622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230622
  have eq243693 : (σ (M.op x y)) = (M.op (σ x) (k (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq163927 eq168054
    | exact resolve eq168054 eq163927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243935 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (σ x) = (k (σ x) X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq168054 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168054
  have eq244021 : (σ (M.op x y)) = (M.op (σ x) (k (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq243693
  have eq244040 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by grind
  clear eq243666
  have eq244116 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq244021 eq135408
    | exact resolve eq135408 eq244021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244119 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) X0) X0) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq244021 eq152142
    | exact resolve eq152142 eq244021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152142
  have eq244178 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq244021 eq35559
    | exact resolve eq35559 eq244021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244744 : (M.op (σ x) (σ (M.op x y))) ≠ (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq244178 eq12
    | (have j0 := eq12 (σ x) (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ (M.op x y))
       have r₂ := eq244178
       grind)
    | exact resolve eq12 eq244178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244804 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq244744
  have eq244865 : ∀ X0 X2 X3 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 X0) X0) X2) (M.op (M.op X0 X2) X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1853 X0 x X2 X3
       have i₂ := eq35559 X0 x
       grind)
    | exact superpose eq35559 eq1853
    | exact resolve eq1853 eq35559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853
  have eq248708 : ∀ X0 X2 X3 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 X2) X3) X3) (M.op (M.op X0 X0) X0)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1854 X0 x X2 X3
       have i₂ := eq35559 X0 x
       grind)
    | exact superpose eq35559 eq1854
    | exact resolve eq1854 eq35559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1854
  have eq259634 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op (M.op X0 X1) X1)) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2244 X0 X1 X2 x
       have i₂ := eq35559 X0 x
       grind)
    | exact superpose eq35559 eq2244
    | exact resolve eq2244 eq35559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2244
  have eq267651 : (σ x) ≠ (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq244178 eq243935
    | (have j0 := eq243935 (σ (M.op x y))
       grind)
    | exact resolve eq243935 eq244178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243935 eq244178
  have eq267675 : (σ x) ≠ (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq267651
  have eq269144 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq267675
       have r₂ := eq244804
       grind)
    | exact resolve eq267675 eq244804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244804 eq267675
  have eq348917 : ∀ X0 X1 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X1) X0) (M.op (M.op X0 X3) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14372 X0 X1 x X3
       have i₂ := eq35559 X0 x
       grind)
    | exact superpose eq35559 eq14372
    | exact resolve eq14372 eq35559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14372
  have eq352057 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) X0) X0) (σ x)) (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ x)))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq244021 eq348917
    | exact resolve eq348917 eq244021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244021 eq348917
  have eq352539 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ x)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq135408 eq352057
    | (have j0 := eq352057 (σ y)
       grind)
    | exact resolve eq352057 eq135408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352057
  have eq353886 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ x)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq136458 eq352539
    | exact resolve eq352539 eq136458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352539
  have eq360715 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) X0) X0) (M.op (M.op (σ (M.op x y)) X0) X0)) = (M.op (M.op (M.op (σ (M.op x y)) X0) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq244119 eq35559
    | exact resolve eq35559 eq244119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244119
  have eq360743 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) X0) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq360715 x
       have i₂ := eq130200 sF1 x
       grind)
    | exact superpose eq130200 eq360715
    | exact resolve eq360715 eq130200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360715
  have eq360892 : (σ (M.op x y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (k (σ (M.op x y)) (σ x))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq244116 eq360743
    | exact resolve eq360743 eq244116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244116 eq360743
  have eq361049 : (σ (M.op x y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (k (σ (M.op x y)) (σ x))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq360892
  have eq362765 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ x)) (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ x))))) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq353886 eq259634
    | exact resolve eq259634 eq353886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259634 eq353886
  have eq362781 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq362765 X0
       have i₂ := eq954 sF2 (M.op sF1 (k sF1 sF2))
       grind)
    | exact superpose eq954 eq362765
    | exact resolve eq362765 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954 eq362765
  have eq362819 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq135408 eq362781
    | exact resolve eq362781 eq135408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362781
  have eq372819 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ x)) (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ x)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq362819 eq117091
    | exact resolve eq117091 eq362819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362819
  have eq372995 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ x)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq51 eq372819
    | exact resolve eq372819 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq372819
  have eq426546 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15189 X0 X1 x
       have i₂ := eq35559 (M.op (M.op X0 X1) X1) x
       grind)
    | exact superpose eq35559 eq15189
    | exact resolve eq15189 eq35559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15189
  have eq426547 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq426546 X0 X1
       have i₂ := eq130200 X0 X1
       grind)
    | exact superpose eq130200 eq426546
    | exact resolve eq426546 eq130200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426546
  have eq426586 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq244040 eq135408
    | exact resolve eq135408 eq244040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244040
  have eq426762 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq426586
       have i₂ := eq35559 sF1 sF2
       grind)
    | exact superpose eq35559 eq426586
    | exact resolve eq426586 eq35559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426586
  have eq432053 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) y) X0) X0) = (M.op (M.op (M.op (M.op x y) y) x) (M.op (M.op (M.op x y) y) x)) := by
    intro X0
    first
    | (have i₁ := eq15765 X0 x
       have i₂ := eq35559 (M.op (M.op sF0 y) x) x
       grind)
    | exact superpose eq35559 eq15765
    | exact resolve eq15765 eq35559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15765
  have eq432054 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) y) X0) X0) := by
    intro X0
    first
    | exact superpose eq135976 eq432053
    | exact resolve eq432053 eq135976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432053
  have eq432055 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq100731 eq432054
    | exact resolve eq432054 eq100731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100731 eq432054
  have eq433930 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X0) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq16158 X0 x
       have i₂ := eq35559 (M.op (M.op sF4 sF3) sF2) x
       grind)
    | exact superpose eq35559 eq16158
    | exact resolve eq16158 eq35559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16158
  have eq433931 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq136458 eq433930
    | exact resolve eq433930 eq136458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433930
  have eq433932 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq99730 eq433931
    | exact resolve eq433931 eq99730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433931
  have eq519207 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) X0) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq426762 eq99730
    | exact resolve eq99730 eq426762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426762
  have eq519426 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq519207 x
       have i₂ := eq69733 sF1 x
       grind)
    | exact superpose eq69733 eq519207
    | exact resolve eq519207 eq69733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519207
  have eq519458 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq433932 eq519426
    | exact resolve eq519426 eq433932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519426
  have eq519549 : (σ (M.op x y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq519458 eq361049
    | exact resolve eq361049 eq519458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361049 eq519458
  have eq519569 : (σ (M.op x y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq519549
  have eq519640 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq99730 eq519569
    | exact resolve eq519569 eq99730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99730 eq519569
  have eq519685 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq433932 eq519640
    | exact resolve eq519640 eq433932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519640
  have eq519686 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq519685
  have eq519704 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq519686 eq107093
    | exact resolve eq107093 eq519686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107093
  have eq519731 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq519686 eq372995
    | exact resolve eq372995 eq519686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372995
  have eq519937 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq519731
  have eq520034 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq519704
       have r₂ := eq27
       grind)
    | exact resolve eq519704 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519704
  have eq526105 : (σ (M.op x y)) = (k (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq519937 eq163927
    | exact resolve eq163927 eq519937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163927 eq519937
  have eq526243 : (σ (M.op x y)) = (k (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq526105
  have eq531668 : x ≠ x ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq520034
       grind)
    | exact superpose eq520034 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq520034
       grind)
    | exact resolve eq13 eq520034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520034
  have eq531751 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq531668
  have eq531793 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq531751
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq531751
    | exact resolve eq531751 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531751
  have eq532945 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13985 y
       have i₂ := eq531793
       grind)
    | exact superpose eq531793 eq13985
    | exact resolve eq13985 eq531793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13985 eq531793
  have eq532963 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq532945
    | exact resolve eq532945 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532945
  have eq532988 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq532963
       have r₂ := eq519686
       grind)
    | exact resolve eq532963 eq519686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519686 eq532963
  have eq532996 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq532988
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq532988
    | exact resolve eq532988 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq532988
  have eq533004 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq532996
    | exact resolve eq532996 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532996
  have eq533009 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq533004
    | exact resolve eq533004 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533004
  have eq533010 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq533009
       have r₂ := eq27
       grind)
    | exact resolve eq533009 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533009
  have eq533212 : (σ (M.op x y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq533010 eq526243
    | exact resolve eq526243 eq533010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526243
  have eq533217 : (σ (M.op x y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq533212
  have eq533290 : (σ (M.op x y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq533217
    | exact resolve eq533217 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq533217
  have eq533456 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq533010 eq533290
    | exact resolve eq533290 eq533010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533010 eq533290
  have eq533477 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq533456
  have eq535084 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq533477 eq269144
    | exact resolve eq269144 eq533477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269144 eq533477
  have eq535179 : (σ (M.op x y)) = (σ x) := by grind
  clear eq535084
  have eq535212 : x = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq535179 eq28
    | exact resolve eq28 eq535179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq535301 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq535179 eq11592
    | exact resolve eq11592 eq535179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11592
  have eq535392 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ (M.op x y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq535179 eq135408
    | exact resolve eq135408 eq535179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135408
  have eq535396 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq535179 eq136458
    | exact resolve eq136458 eq535179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136458
  have eq535419 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq535179 eq433932
    | exact resolve eq433932 eq535179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433932
  have eq535502 : x = (M.op x y) := by
    first
    | exact superpose eq30 eq535212
    | exact resolve eq535212 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq535212
  have eq536206 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq535502 eq135976
    | exact resolve eq135976 eq535502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135976
  have eq536227 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op (M.op x y) X0) (M.op (M.op x X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq535502 eq148417
    | exact resolve eq148417 eq535502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148417
  have eq536693 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op (M.op x y) X0) (M.op (M.op x X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq536227 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq536227
    | (have j0 := eq536227 X0 X1
       grind)
    | exact resolve eq536227 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536227
  have eq536697 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq536206
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq536206
    | exact resolve eq536206 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536206
  have eq536902 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op x X0) (M.op (M.op x X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq535502 eq536693
    | exact resolve eq536693 eq535502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536693
  have eq536906 : x = (M.op x x) := by
    first
    | exact superpose eq535502 eq536697
    | exact resolve eq536697 eq535502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536697
  have eq537009 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x X0) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq536902 X0 x
       have i₂ := eq35559 (M.op x X0) x
       grind)
    | exact superpose eq35559 eq536902
    | exact resolve eq536902 eq35559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536902
  have eq538568 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq535396 eq244865
    | exact resolve eq244865 eq535396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244865
  have eq538959 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k (M.op (σ x) (σ y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq535419 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq13 eq535419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535419
  have eq566681 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op x X0) (M.op x X0)) (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq149539 X0 (M.op x X0)
       have i₂ := eq537009 X0
       grind)
    | exact superpose eq537009 eq149539
    | exact resolve eq149539 eq537009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149539
  have eq566768 : ∀ X0 X1 : G, (M.op x X0) ≠ (k (M.op x X0) (σ X1)) ∨ (k (M.op x X0) (σ X1)) = (M.op (M.op x X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14015 (M.op x X0) X1
       have i₂ := eq537009 X0
       grind)
    | exact superpose eq537009 eq14015
    | (have j0 := eq14015 (M.op x X0) X1
       grind)
    | exact resolve eq14015 eq537009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14015
  have eq566943 : ∀ X0 X1 : G, (k (M.op x X0) (σ X1)) = (M.op (M.op x X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq566768 X0 X1
       have j1 := eq17873 (M.op x X0) X1
       grind)
    | (have r₁ := eq566768 X0 X1
       have r₂ := eq17873 (M.op x X0) X1
       grind)
    | exact resolve eq566768 eq17873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17873 eq566768
  have eq566980 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op x X0) (M.op x X0)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq535502 eq566681
    | exact resolve eq566681 eq535502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566681
  have eq567079 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op x X0) (M.op x X0)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq566980 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq566980
    | (have j0 := eq566980 X0
       grind)
    | exact resolve eq566980 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566980
  have eq567152 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op x X0) (M.op x X0)) x) := by
    intro X0
    first
    | exact superpose eq535502 eq567079
    | exact resolve eq567079 eq535502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567079
  have eq567212 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq567152 X0
       have i₂ := eq537009 X0
       grind)
    | exact superpose eq537009 eq567152
    | exact resolve eq567152 eq537009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537009 eq567152
  have eq568807 : ∀ X0 : G, x ≠ (M.op x X0) ∨ (M.op x (M.op x X0)) = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq13 x (M.op x X0)
       have i₂ := eq567212 X0
       grind)
    | exact superpose eq567212 eq13
    | (have j0 := eq13 x (M.op x X0)
       grind)
    | exact resolve eq13 eq567212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq568957 : ∀ X0 : G, (M.op x (M.op x y)) = (k x (M.op x X0)) ∨ x ≠ (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq568807 X0
       have i₂ := eq1196 X0
       grind)
    | (have i₁ := eq568807 y
       have i₂ := eq1196 X0
       grind)
    | exact superpose eq1196 eq568807
    | (have j0 := eq568807 X0
       grind)
    | exact resolve eq568807 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196 eq568807
  have eq569102 : ∀ X0 : G, (M.op x x) = (k x (M.op x X0)) ∨ x ≠ (M.op x X0) := by
    intro X0
    first
    | exact superpose eq432055 eq568957
    | (have j0 := eq568957 X0
       grind)
    | exact resolve eq568957 eq432055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568957
  have eq569217 : ∀ X0 : G, x = (k x (M.op x X0)) ∨ x ≠ (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq569102 X0
       have i₂ := eq536906
       grind)
    | exact superpose eq536906 eq569102
    | (have j0 := eq569102 X0
       grind)
    | (have r₁ := eq569102 x
       have r₂ := eq536906
       grind)
    | exact resolve eq569102 eq536906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569102
  have eq616277 : ∀ X1 : G, (M.op x x) ≠ (M.op x (M.op x y)) ∨ x = (M.op (M.op x X1) x) ∨ x = (k x (M.op x X1)) := by
    intro X1
    first
    | (have i₁ := eq2234 x x X1
       have i₂ := eq1186 x
       grind)
    | exact superpose eq1186 eq2234
    | (have j0 := eq2234 x X1 X1
       grind)
    | exact resolve eq2234 eq1186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186 eq2234
  have eq616326 : ∀ X1 : G, x = (M.op (M.op x X1) x) ∨ x = (k x (M.op x X1)) := by
    intro X1
    first
    | (have j0 := eq616277 X1
       grind)
    | (have r₁ := eq616277 X1
       have r₂ := eq432055
       grind)
    | exact resolve eq616277 eq432055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432055 eq616277
  have eq616775 : ∀ X1 : G, x = (k x (M.op x X1)) ∨ x = (M.op x X1) := by
    intro X1
    first
    | (have i₁ := eq616326 X1
       have i₂ := eq567212 X1
       grind)
    | exact superpose eq567212 eq616326
    | (have j0 := eq616326 X1
       grind)
    | exact resolve eq616326 eq567212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616326
  have eq626613 : ∀ X0 : G, x = (k x (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq569217 X0
       have j1 := eq616775 X0
       grind)
    | (have r₁ := eq569217 x
       have r₂ := eq616775 x
       grind)
    | exact resolve eq569217 eq616775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569217 eq616775
  have eq648223 : (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ (M.op x y))) (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq538568 eq130200
    | exact resolve eq130200 eq538568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130200 eq538568
  have eq648260 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq535396 eq648223
    | exact resolve eq648223 eq535396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535396 eq648223
  have eq648437 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq648260 eq1884
    | exact resolve eq1884 eq648260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1884 eq648260
  have eq648730 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq648437 eq69733
    | exact resolve eq69733 eq648437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq648804 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) X0) (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq648437 eq248708
    | exact resolve eq248708 eq648437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248708 eq648437
  have eq648835 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq648804 X0
       have i₂ := eq69733 sF1 (M.op sF1 sF1)
       grind)
    | exact superpose eq69733 eq648804
    | exact resolve eq648804 eq69733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648804
  have eq648903 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq648835 x
       have i₂ := eq69733 sF4 x
       grind)
    | exact superpose eq69733 eq648835
    | exact resolve eq648835 eq69733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648835
  have eq649318 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq648903 eq648730
    | exact resolve eq648730 eq648903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648730
  have eq657172 : ∀ X0 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X2) X2) ∨ (M.op (M.op (M.op X0 X2) X2) X0) = (k (M.op (M.op X0 X2) X2) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq2293 X0 x X2
       have i₂ := eq35559 X0 x
       grind)
    | exact superpose eq35559 eq2293
    | (have j0 := eq2293 X0 x X2
       grind)
    | exact resolve eq2293 eq35559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2293 eq35559
  have eq657173 : ∀ X0 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X2) X2) ∨ (k (M.op (M.op X0 X2) X2) X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq657172 X0 X2
       have i₂ := eq426547 X0 X2
       grind)
    | exact superpose eq426547 eq657172
    | (have j0 := eq657172 X0 X2
       grind)
    | exact resolve eq657172 eq426547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426547 eq657172
  have eq681614 : ∀ X0 : G, (k x (σ X0)) = (M.op x (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq566943 x x
       have i₂ := eq536906
       grind)
    | exact superpose eq536906 eq566943
    | exact resolve eq566943 eq536906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536906
  have eq681675 : ∀ X0 X1 : G, (k (M.op x X1) X0) = (M.op (M.op x X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq566943 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq566943
    | exact resolve eq566943 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566943
  have eq682339 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq681614 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq681614
    | exact resolve eq681614 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681614
  have eq683288 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op x (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq682339 (τ X0)
       grind)
    | exact superpose eq682339 eq42
    | exact resolve eq42 eq682339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq683290 : ∀ X0 : G, (k (σ x) (k (σ x) X0)) = (σ (k x (M.op x (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq348 x X0
       have i₂ := eq682339 (τ X0)
       grind)
    | exact superpose eq682339 eq348
    | exact resolve eq348 eq682339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq683295 : ∀ X0 : G, (k (k (σ x) X0) (σ (M.op x y))) = (σ (k (M.op x (τ X0)) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq353 x X0
       have i₂ := eq682339 (τ X0)
       grind)
    | exact superpose eq682339 eq353
    | exact resolve eq353 eq682339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq683543 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq682339 y
       grind)
    | exact superpose eq682339 eq44
    | exact resolve eq44 eq682339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq682339
  have eq683610 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq535179 eq683543
    | exact resolve eq683543 eq535179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683543
  have eq683776 : ∀ X0 : G, (k (k (σ x) X0) (σ (M.op x y))) = (σ (k (M.op x (τ X0)) x)) := by
    intro X0
    first
    | exact superpose eq535502 eq683295
    | exact resolve eq683295 eq535502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535502 eq683295
  have eq683781 : ∀ X0 : G, (σ x) = (k (σ x) (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq683290 X0
       have i₂ := eq626613 (τ X0)
       grind)
    | exact superpose eq626613 eq683290
    | exact resolve eq683290 eq626613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626613 eq683290
  have eq683783 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (σ (M.op x (τ X0))) := by
    intro X0
    first
    | exact superpose eq535179 eq683288
    | exact resolve eq683288 eq535179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683288
  have eq683857 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq683610
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq683610
    | exact resolve eq683610 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq683610
  have eq684000 : ∀ X0 : G, (k (k (σ x) X0) (σ (M.op x y))) = (σ (k (M.op x (τ X0)) x)) := by
    intro X0
    first
    | (have i₁ := eq683776 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq683776
    | (have j0 := eq683776 X0
       grind)
    | exact resolve eq683776 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683776
  have eq684005 : ∀ X0 : G, (σ x) = (k (σ x) (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq683781 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq683781
    | (have j0 := eq683781 X0
       grind)
    | exact resolve eq683781 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq683781
  have eq684059 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq683857
    | exact resolve eq683857 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq683857
  have eq684154 : ∀ X0 : G, (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = (σ (k (M.op x (τ X0)) x)) := by
    intro X0
    first
    | exact superpose eq535179 eq684000
    | exact resolve eq684000 eq535179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684000
  have eq684157 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq535179 eq684005
    | exact resolve eq684005 eq535179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535179 eq684005
  have eq684414 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq684059 eq535301
    | exact resolve eq535301 eq684059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535301 eq684059
  have eq684426 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq684414
       have r₂ := eq27
       grind)
    | exact resolve eq684414 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684414
  have eq684456 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (M.op (σ x) (σ y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq684426 eq538959
    | (have r₁ := eq538959
       have r₂ := eq684426
       grind)
    | exact resolve eq538959 eq684426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538959
  have eq684489 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq684426 eq535392
    | exact resolve eq535392 eq684426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535392
  have eq684507 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq684426 eq69733
    | exact resolve eq69733 eq684426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69733
  have eq684612 : (k (M.op (σ x) (σ y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by grind
  clear eq684456
  have eq685636 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq684157 (M.op (M.op sF1 sF1) sF1)
       have i₂ := eq117091 sF1
       grind)
    | exact superpose eq117091 eq684157
    | exact resolve eq684157 eq117091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684157
  have eq685734 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq684426 eq685636
    | exact resolve eq685636 eq684426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685636
  have eq688274 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ≠ (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq684489 eq657173
    | exact resolve eq657173 eq684489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657173 eq684489
  have eq688277 : (σ (M.op x y)) ≠ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq649318 eq688274
    | exact resolve eq688274 eq649318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688274
  have eq688395 : (σ (M.op x y)) ≠ (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (k (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq648903 eq688277
    | exact resolve eq688277 eq648903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648903 eq688277
  have eq688474 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) ≠ (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq649318 eq688395
    | exact resolve eq688395 eq649318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649318 eq688395
  have eq688521 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq685734 eq688474
    | exact resolve eq688474 eq685734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685734 eq688474
  have eq688545 : (σ (M.op x y)) ≠ (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq688521
       have r₂ := eq27
       grind)
    | exact resolve eq688521 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq688521
  have eq847511 : ∀ X0 : G, (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = (σ (M.op (M.op x (τ X0)) x)) := by
    intro X0
    first
    | (have i₁ := eq684154 X0
       have i₂ := eq681675 x (τ X0)
       grind)
    | exact superpose eq681675 eq684154
    | exact resolve eq684154 eq681675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681675 eq684154
  have eq847512 : ∀ X0 : G, (σ (M.op x (τ X0))) = (k (k (σ (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq847511 X0
       have i₂ := eq567212 (τ X0)
       grind)
    | exact superpose eq567212 eq847511
    | exact resolve eq847511 eq567212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567212 eq847511
  have eq847513 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (k (k (σ (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq847512 X0
       have i₂ := eq683783 X0
       grind)
    | exact superpose eq683783 eq847512
    | exact resolve eq847512 eq683783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683783 eq847512
  have eq847525 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq847513 (M.op (M.op sF1 sF1) sF1)
       have i₂ := eq117091 sF1
       grind)
    | exact superpose eq117091 eq847513
    | exact resolve eq847513 eq117091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117091 eq847513
  have eq847621 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq684426 eq847525
    | exact resolve eq847525 eq684426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684426 eq847525
  have eq847633 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq684612 eq847621
    | exact resolve eq847621 eq684612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684612 eq847621
  have eq847747 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq847633 eq684507
    | exact resolve eq684507 eq847633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684507 eq847633
  have eq847945 : False := by grind
  exact eq847945

/-- `Equation2062`: `x = ((x ◇ y) ◇ y) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxx_x_pxy_Equation2062 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2062 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2062.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X2)) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op (M.op x y) y) (M.op x X0)) := by
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
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 (M.op X0 X2)) (M.op (M.op (M.op X0 X1) X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X1) (M.op X0 X2) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 (M.op X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X1)) (M.op X0 X1) X2
       have i₂ := eq14 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, x = (M.op (M.op (M.op x X0) X0) (M.op x y)) := by
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
  have eq55 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) X0) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (M.op (M.op (M.op X0 X1) X1) X2) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X1) X2 (M.op X0 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq97 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
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
  have eq102 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
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
  have eq113 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq102
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
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
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq118
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq118
    | exact resolve eq118 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq214 : x = (M.op (M.op (M.op x y) y) (M.op x y)) := by
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
  have eq223 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq239 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0)) := by
    intro X0
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq429 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq260 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq260
    | exact resolve eq260 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq445 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq260 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq260
    | (have j0 := eq260 X0 y
       grind)
    | exact resolve eq260 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq685 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X0 (M.op X0 X1)) X2)) = (M.op (M.op (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X0 (M.op X0 X1)) X2)) X3) X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X0 (M.op (M.op X0 (M.op X0 X1)) X2) X2
       have i₂ := eq53 X0 X1 X2
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X1) X2) X2) = (M.op (M.op (M.op (M.op X0 X1) X1) X0) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 (M.op (M.op X0 X1) X1) X2 X0
       have i₂ := eq56 X0 X1 X2
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq703 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 (M.op X0 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X0 X1 (M.op X0 X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq704 : ∀ X0 : G, (M.op (M.op x X0) X0) = (M.op (M.op x (M.op x y)) x) := by
    intro X0
    first
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq705 : ∀ X0 : G, (M.op (M.op (σ x) X0) X0) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq707 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56 (M.op X0 X0) X0 X0
       have i₂ := eq56 X0 X0 X0
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq714 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq707 X0
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq707
    | exact resolve eq707 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq716 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X0 X1
       have i₂ := eq714 X0
       grind)
    | exact superpose eq714 eq14
    | exact resolve eq14 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq720 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op (M.op X0 X0) X0)
       have i₂ := eq714 X0
       grind)
    | exact superpose eq714 eq13
    | (have j0 := eq13 X0 (M.op (M.op X0 X0) X0)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq714 X0
       grind)
    | exact resolve eq13 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq723 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq720 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq728 : ∀ X0 X1 : G, (M.op (M.op x X0) X0) = (M.op (M.op x X1) X1) := by
    intro X0 X1
    first
    | exact superpose eq704 eq704
    | exact resolve eq704 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq803 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X2)) = (M.op X0 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X2 (M.op (M.op (M.op X0 X1) X1) x)
       have i₂ := eq52 X0 X1 X2 x
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq53
  have eq975 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq993 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq975 X0 X1
       have j1 := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq975 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq975 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq975 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975
  have eq1003 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq993 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq993
    | (have j0 := eq993 X0 X1
       grind)
    | exact resolve eq993 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993
  have eq1011 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | (have i₁ := eq728 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq728
    | (have j0 := eq728 y X0
       grind)
    | exact resolve eq728 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq1081 : x = (M.op (M.op (M.op x y) y) x) := by
    first
    | (have i₁ := eq714 x
       have i₂ := eq1011 x
       grind)
    | exact superpose eq1011 eq714
    | exact resolve eq714 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1082 : (M.op x x) = (M.op x (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq716 x x
       have i₂ := eq1011 x
       grind)
    | exact superpose eq1011 eq716
    | exact resolve eq716 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq1256 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq223 eq226
    | exact resolve eq226 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq1275 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | exact superpose eq705 eq1256
    | exact resolve eq1256 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq1278 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq1256 eq239
    | exact resolve eq239 eq1256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239 eq1256
  have eq1297 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by
    first
    | exact superpose eq1275 eq714
    | exact resolve eq714 eq1275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1298 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq1275 eq716
    | exact resolve eq716 eq1275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1352 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1278 eq1298
    | exact resolve eq1298 eq1278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298
  have eq1393 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) y) X0) X0) = (M.op (M.op (M.op (M.op x y) y) x) (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq214 eq703
    | exact resolve eq703 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq1400 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X0) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq223 eq703
    | exact resolve eq703 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1415 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq703 X0 X1 x
       have i₂ := eq703 X0 X2 x
       grind)
    | exact superpose eq703 eq703
    | exact resolve eq703 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq1459 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X0) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq1297 eq1400
    | exact resolve eq1400 eq1297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400
  have eq1464 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) y) X0) X0) = (M.op x (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq1081 eq1393
    | exact resolve eq1393 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393
  have eq1487 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X0) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1278 eq1459
    | exact resolve eq1459 eq1278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1459
  have eq1491 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) y) X0) X0) := by
    intro X0
    first
    | exact superpose eq1082 eq1464
    | exact resolve eq1464 eq1082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082 eq1464
  have eq1671 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq803 X0 X0 X1
       have i₂ := eq716 X0 X0
       grind)
    | exact superpose eq716 eq803
    | exact resolve eq803 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq1927 : (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq223 eq1671
    | exact resolve eq1671 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq1994 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq1297 eq1927
    | exact resolve eq1927 eq1297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297 eq1927
  have eq2037 : (σ x) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    first
    | exact superpose eq1994 eq723
    | exact resolve eq723 eq1994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1994
  have eq2040 : (σ x) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1278 eq2037
    | exact resolve eq2037 eq1278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278 eq2037
  have eq2049 : (σ x) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq1352 eq2040
    | exact resolve eq2040 eq1352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040
  have eq2281 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1415 (M.op X0 X0) X0 X1
       have i₂ := eq714 X0
       grind)
    | exact superpose eq714 eq1415
    | exact resolve eq1415 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2366 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq714 X0
       have i₂ := eq1415 X0 X0 X1
       grind)
    | (have i₁ := eq714 X0
       have i₂ := eq1415 X0 X1 X0
       grind)
    | exact superpose eq1415 eq714
    | exact resolve eq714 eq1415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq2378 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq716 X0 X0
       have i₂ := eq1415 X0 X0 X1
       grind)
    | (have i₁ := eq716 X0 X0
       have i₂ := eq1415 X0 X1 X0
       grind)
    | exact superpose eq1415 eq716
    | exact resolve eq716 eq1415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq3342 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq1352 eq1487
    | exact resolve eq1487 eq1352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1487
  have eq3343 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) X0) X0) y) := by
    intro X0
    first
    | (have i₁ := eq1491 y
       have i₂ := eq1415 sF0 y x
       grind)
    | (have i₁ := eq1491 y
       have i₂ := eq1415 sF0 x y
       grind)
    | exact superpose eq1415 eq1491
    | exact resolve eq1491 eq1415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1491
  have eq4252 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3342 sF3
       have i₂ := eq1415 sF4 sF3 x
       grind)
    | (have i₁ := eq3342 sF3
       have i₂ := eq1415 sF4 x sF3
       grind)
    | exact superpose eq1415 eq3342
    | exact resolve eq3342 eq1415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1415 eq3342
  have eq5366 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq97 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq97
    | (have j0 := eq97 x
       grind)
    | exact resolve eq97 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq5400 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5366
  have eq5419 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5400
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq5400
    | exact resolve eq5400 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq5400
  have eq5435 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq5419
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq5419 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5419
  have eq5440 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5435 eq49
    | exact resolve eq49 eq5435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq7217 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X1) X2) X2) = (M.op X0 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq702 X0 X1 X2
       have i₂ := eq2366 X0 X1
       grind)
    | exact superpose eq2366 eq702
    | exact resolve eq702 eq2366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq7218 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7217 X0 X1 X2
       have i₂ := eq2378 X0 X1
       grind)
    | exact superpose eq2378 eq7217
    | exact resolve eq7217 eq2378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2378 eq7217
  have eq14160 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) = (M.op (M.op (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) X3) X3) X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq685 X0 X1 X1 X3
       have i₂ := eq1671 (M.op X0 (M.op X0 X1)) X1
       grind)
    | exact superpose eq1671 eq685
    | exact resolve eq685 eq1671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq14161 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq14160 X0 X1 x
       have i₂ := eq2281 (M.op X0 (M.op X0 X1)) x
       grind)
    | exact superpose eq2281 eq14160
    | exact resolve eq14160 eq2281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14160
  have eq14162 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq14161 X0 x
       have i₂ := eq1671 X0 x
       grind)
    | exact superpose eq1671 eq14161
    | exact resolve eq14161 eq1671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14161
  have eq14534 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq723 (M.op X0 X0)
       have i₂ := eq14162 X0
       grind)
    | exact superpose eq14162 eq723
    | exact resolve eq723 eq14162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723 eq14162
  have eq14592 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq14534 X0
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq14534
    | exact resolve eq14534 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14534
  have eq29841 : (σ (M.op x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq5435 eq113
    | exact resolve eq113 eq5435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq5435
  have eq29909 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq119 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29921 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq29909
    | exact resolve eq29909 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29909
  have eq29928 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq29921
       have r₂ := eq27
       grind)
    | exact resolve eq29921 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29921
  have eq29930 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq29928
    | exact resolve eq29928 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29928
  have eq29954 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) (σ x)) X0) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq29930 eq7218
    | exact resolve eq7218 eq29930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29930
  have eq29975 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq29954 x
       have i₂ := eq2281 sF2 x
       grind)
    | exact superpose eq2281 eq29954
    | exact resolve eq29954 eq2281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29954
  have eq30002 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29975 eq14592
    | exact resolve eq14592 eq29975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29975
  have eq30071 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq30002
    | exact resolve eq30002 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30002
  have eq31039 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30071 eq119
    | exact resolve eq119 eq30071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq30071
  have eq31054 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq31039
  have eq31056 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq31054
       have r₂ := eq27
       grind)
    | exact resolve eq31054 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31054
  have eq31080 : ∀ X0 : G, (M.op y y) = (M.op (M.op (M.op x x) X0) X0) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq7218 y x X0
       have i₂ := eq31056
       grind)
    | exact superpose eq31056 eq7218
    | exact resolve eq7218 eq31056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31056
  have eq31101 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31080 x
       have i₂ := eq2281 x x
       grind)
    | exact superpose eq2281 eq31080
    | exact resolve eq31080 eq2281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31080
  have eq31232 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14592 y
       have i₂ := eq31101
       grind)
    | exact superpose eq31101 eq14592
    | exact resolve eq14592 eq31101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31101
  have eq31300 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31232
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq31232
    | exact resolve eq31232 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31232
  have eq31917 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq31300
       grind)
    | exact superpose eq31300 eq44
    | exact resolve eq44 eq31300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq31300
  have eq31953 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq31917
    | exact resolve eq31917 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31917
  have eq32132 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31953 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq31953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32146 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq32132
    | exact resolve eq32132 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32132
  have eq32153 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq32146
       have r₂ := eq27
       grind)
    | exact resolve eq32146 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32146
  have eq32155 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq32153
    | exact resolve eq32153 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32153
  have eq32156 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq32155
  have eq32182 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) (σ x)) X0) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq32156 eq7218
    | exact resolve eq7218 eq32156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32156
  have eq32203 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq32182 x
       have i₂ := eq2281 sF2 x
       grind)
    | exact superpose eq2281 eq32182
    | exact resolve eq32182 eq2281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32182
  have eq32228 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32203 eq14592
    | exact resolve eq14592 eq32203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32203
  have eq32297 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq32228
    | exact resolve eq32228 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32228
  have eq32766 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32297 eq31953
    | exact resolve eq31953 eq32297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31953 eq32297
  have eq32779 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32766
  have eq32783 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq32779
       have r₂ := eq27
       grind)
    | exact resolve eq32779 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32779
  have eq32789 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32783 eq79
    | (have r₁ := eq79
       have r₂ := eq32783
       grind)
    | exact resolve eq79 eq32783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq32799 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32783 eq1352
    | exact resolve eq1352 eq32783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1352
  have eq32809 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ y) X0) X0) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq32783 eq4252
    | exact resolve eq4252 eq32783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4252 eq32783
  have eq32836 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq32789
  have eq32839 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq32809 x
       have i₂ := eq2366 sF3 x
       grind)
    | exact superpose eq2366 eq32809
    | exact resolve eq32809 eq2366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32809
  have eq32844 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq32799
    | exact resolve eq32799 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32799
  have eq32867 : (τ (σ y)) = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32839 eq5440
    | exact resolve eq5440 eq32839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32877 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32839 eq1275
    | exact resolve eq1275 eq32839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1275 eq32839
  have eq32961 : y = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq32867
    | exact resolve eq32867 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq32867
  have eq32976 : (σ x) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32844 eq2049
    | exact resolve eq2049 eq32844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2049
  have eq32979 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32844 eq5440
    | exact resolve eq5440 eq32844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5440 eq32844
  have eq33197 : y = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq32961
       have i₂ := eq32979
       grind)
    | exact superpose eq32979 eq32961
    | exact resolve eq32961 eq32979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32979
  have eq33222 : y = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq33197
  have eq33301 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq33222 eq429
    | exact resolve eq429 eq33222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429 eq33222
  have eq33308 : ∀ X0 : G, (τ (k X0 (σ y))) = (τ (k X0 (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq33301 X0
       have i₂ := eq445 X0
       grind)
    | exact superpose eq445 eq33301
    | exact resolve eq33301 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445 eq33301
  have eq36395 : (σ x) = (k (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32877 eq32976
    | exact resolve eq32976 eq32877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32877 eq32976
  have eq36419 : (σ x) = (k (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq36395
  have eq56620 : (τ (σ x)) = (τ (k (M.op (σ y) (σ x)) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36419 eq33308
    | exact resolve eq33308 eq36419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33308 eq36419
  have eq56709 : (τ (σ x)) = (τ (k (M.op (σ y) (σ x)) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq56620
  have eq56770 : x = (τ (k (M.op (σ y) (σ x)) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq56709
    | exact resolve eq56709 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56709
  have eq106775 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32836 eq60
    | exact resolve eq60 eq32836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32836
  have eq106820 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq106775
    | exact resolve eq106775 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq106775
  have eq107576 : x = (τ (k (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq106820 eq56770
    | exact resolve eq56770 eq106820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56770 eq106820
  have eq107677 : x = (τ (k (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (k x y) := by grind
  clear eq107576
  have eq107747 : x = (k x y) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq60 eq107677
    | exact resolve eq107677 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq107677
  have eq107748 : x = (k x y) ∨ y = (M.op x y) := by grind
  clear eq107747
  have eq107800 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq107748
       grind)
    | exact superpose eq107748 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq107748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107821 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq107800
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107800
    | exact resolve eq107800 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107800
  have eq107838 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq107821
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107821
    | exact resolve eq107821 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107821
  have eq107839 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq107838
  have eq108280 : ∀ X0 : G, (M.op y y) = (M.op (M.op (M.op x x) X0) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7218 y x X0
       have i₂ := eq107839
       grind)
    | exact superpose eq107839 eq7218
    | exact resolve eq7218 eq107839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7218 eq107839
  have eq108318 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq108280 x
       have i₂ := eq2281 x x
       grind)
    | exact superpose eq2281 eq108280
    | exact resolve eq108280 eq2281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2281 eq108280
  have eq109256 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14592 y
       have i₂ := eq108318
       grind)
    | exact superpose eq108318 eq14592
    | exact resolve eq14592 eq108318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14592 eq108318
  have eq109346 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq109256
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq109256
    | exact resolve eq109256 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109256
  have eq114171 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq107748
       have i₂ := eq109346
       grind)
    | exact superpose eq109346 eq107748
    | exact resolve eq107748 eq109346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107748 eq109346
  have eq114184 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq114171
  have eq114259 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq114184 eq20
    | exact resolve eq20 eq114184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114375 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op y X0) X0) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq114184 eq3343
    | exact resolve eq3343 eq114184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3343
  have eq114419 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq114184
  have eq114438 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq114375 x
       have i₂ := eq2366 y x
       grind)
    | exact superpose eq2366 eq114375
    | exact resolve eq114375 eq2366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2366 eq114375
  have eq114538 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq114259
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq114259
    | exact resolve eq114259 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114259
  have eq114924 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29841
       have i₂ := eq114438
       grind)
    | exact superpose eq114438 eq29841
    | exact resolve eq29841 eq114438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29841 eq114438
  have eq115048 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq114924
       have r₂ := eq114419
       grind)
    | exact resolve eq114924 eq114419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114419 eq114924
  have eq115058 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq115048
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq115048
    | exact resolve eq115048 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115048
  have eq115423 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115058 eq1671
    | exact resolve eq1671 eq115058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1671 eq115058
  have eq115467 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq115423
    | exact resolve eq115423 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115423
  have eq115503 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115467 eq27
    | exact resolve eq27 eq115467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115467
  have eq115753 : x = (M.op x y) := by
    first
    | (have r₁ := eq115503
       have r₂ := eq114538
       grind)
    | exact resolve eq115503 eq114538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114538 eq115503
  have eq115759 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq115753 eq20
    | exact resolve eq20 eq115753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq115821 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq115753 eq1081
    | exact resolve eq1081 eq115753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081
  have eq116006 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq115821
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115821
    | exact resolve eq115821 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq115821
  have eq116062 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq115759
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq115759
    | exact resolve eq115759 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115759
  have eq116090 : x = (M.op x x) := by
    first
    | exact superpose eq115753 eq116006
    | exact resolve eq116006 eq115753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116006
  have eq116147 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq116062 eq26
    | exact resolve eq26 eq116062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq116713 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq116090
       grind)
    | exact superpose eq116090 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq116090
       grind)
    | exact resolve eq13 eq116090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116090
  have eq116759 : x = (k x x) := by grind
  clear eq116713
  have eq117082 : x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq32961
       have i₂ := eq116759
       grind)
    | exact superpose eq116759 eq32961
    | exact resolve eq32961 eq116759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32961
  have eq117097 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1003 x x
       have i₂ := eq116759
       grind)
    | exact superpose eq116759 eq1003
    | (have j0 := eq1003 x x
       grind)
    | exact resolve eq1003 eq116759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003 eq116759
  have eq117103 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq117097
  have eq117104 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq117103
  have eq117120 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq117104
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq117104
    | exact resolve eq117104 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117104
  have eq117129 : x = y ∨ x = y := by
    first
    | exact superpose eq115753 eq117082
    | exact resolve eq117082 eq115753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115753 eq117082
  have eq117130 : x = y := by grind
  clear eq117129
  have eq117143 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq116062 eq117120
    | exact resolve eq117120 eq116062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117120
  have eq117189 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq117130
       grind)
    | exact superpose eq117130 eq24
    | exact resolve eq24 eq117130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq117130
  have eq117484 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq117189
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq117189
    | exact resolve eq117189 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq117189
  have eq117610 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq116062 eq117484
    | exact resolve eq117484 eq116062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116062 eq117484
  have eq118064 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq117610 eq116147
    | exact resolve eq116147 eq117610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116147 eq117610
  have eq119464 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq117143 eq118064
    | exact resolve eq118064 eq117143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117143 eq118064
  have eq119465 : False := by grind
  exact eq119465

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pyx_pxx_pyx_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq36 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
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
  have eq41 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq54 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq55 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq36 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq64 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq54 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq54 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq177 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq643 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq55 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq644 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq643 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq649 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq644 X0 X1
       have j1 := eq177 X0 X1
       grind)
    | (have r₁ := eq644 X0 X1
       have r₂ := eq177 X0 X1
       grind)
    | (have r₁ := eq644 X1 X1
       have r₂ := eq177 X1 X1
       grind)
    | exact resolve eq644 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq644
  have eq1063 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq649 (σ X1) (σ X0)
       grind)
    | exact superpose eq649 eq15
    | exact resolve eq15 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1066 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1063 X0 X1
       have i₂ := eq649 X1 X0
       grind)
    | exact superpose eq649 eq1063
    | exact resolve eq1063 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649 eq1063
  have eq1070 : False := by grind
  exact eq1070

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxy_pxx_pxy_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq9 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) ≠ X2 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 X2
       have i₂ := eq21 X0 X2 X1
       grind)
    | (have i₁ := eq12 X0 (M.op X2 X2)
       have i₂ := eq21 X2 X1 X2
       grind)
    | exact superpose eq21 eq12
    | (have j0 := eq12 X3 X2
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X0 X0) (M.op X2 X2))
       have r₂ := eq21 X0 (M.op (M.op X0 X0) (M.op X2 X2)) X2
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq21 X1 X1 X1
       grind)
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = X3 ∨ (M.op X3 X3) = X3 ∨ (k X2 X3) = (M.op X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3
       have i₂ := eq21 X0 X2 X1
       grind)
    | (have i₁ := eq14 (M.op X2 X2) X1
       have i₂ := eq21 X2 X1 X2
       grind)
    | exact superpose eq21 eq14
    | (have j0 := eq14 X3 X3
       grind)
    | exact resolve eq14 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq106 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = X3 ∨ (k X2 X3) = (M.op X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq93 X0 X1 X2 X3
       have j1 := eq12 X2 X3
       grind)
    | (have r₁ := eq93 X0 X0 X2 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq93 X0 X1 X2 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1)))
       have r₂ := eq12 X0 (M.op (M.op X0 X0) (M.op X1 X1))
       grind)
    | (have r₁ := eq93 X0 X1 X2 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq93 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq112 : ∀ X2 X3 : G, (k X2 X3) = (M.op X2 X3) := by
    intro X2 X3
    first
    | (have j0 := eq106 x x X2 X3
       have j1 := eq91 x x X3 X2
       grind)
    | (have r₁ := eq106 x x X2 X2
       have r₂ := eq91 x x X2 X3
       grind)
    | (have r₁ := eq106 x x X2 (M.op (M.op x x) (M.op x x))
       have r₂ := eq91 x x (M.op (M.op x x) (M.op x x)) X3
       grind)
    | (have r₁ := eq106 x x (M.op x x) (M.op x x)
       have r₂ := eq91 x x (k (M.op x x) (M.op x x)) X3
       grind)
    | exact resolve eq106 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq106
  have eq337 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq112 (σ X0) (σ X1)
       grind)
    | exact superpose eq112 eq15
    | exact resolve eq15 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq337 X0 X1
       have i₂ := eq112 X0 X1
       grind)
    | exact superpose eq112 eq337
    | exact resolve eq337 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq337
  have eq345 : False := by grind
  exact eq345

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyx_pxx_pyx_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq9 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) ≠ X2 ∨ (k X3 X2) = (M.op X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 X2
       have i₂ := eq21 X0 X2 X1
       grind)
    | (have i₁ := eq12 X0 (M.op X2 X2)
       have i₂ := eq21 X2 X1 X2
       grind)
    | exact superpose eq21 eq12
    | (have j0 := eq12 X3 X2
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X0 X0) (M.op X2 X2))
       have r₂ := eq21 X0 (M.op (M.op X0 X0) (M.op X2 X2)) X2
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq21 X1 X1 X1
       grind)
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = X3 ∨ (M.op X3 X3) = X3 ∨ (k X2 X3) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3
       have i₂ := eq21 X0 X2 X1
       grind)
    | (have i₁ := eq14 (M.op X2 X2) X1
       have i₂ := eq21 X2 X1 X2
       grind)
    | exact superpose eq21 eq14
    | (have j0 := eq14 X3 X3
       grind)
    | exact resolve eq14 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq106 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = X3 ∨ (k X2 X3) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq93 X0 X1 X2 X3
       have j1 := eq12 X2 X3
       grind)
    | (have r₁ := eq93 X0 X0 X2 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq93 X0 X1 X2 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1)))
       have r₂ := eq12 X0 (M.op (M.op X0 X0) (M.op X1 X1))
       grind)
    | (have r₁ := eq93 X0 X1 X2 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq93 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq112 : ∀ X2 X3 : G, (k X2 X3) = (M.op X3 X2) := by
    intro X2 X3
    first
    | (have j0 := eq106 x x X2 X3
       have j1 := eq91 x x X3 X2
       grind)
    | (have r₁ := eq106 x x X2 X2
       have r₂ := eq91 x x X2 X3
       grind)
    | (have r₁ := eq106 x x X2 (M.op (M.op x x) (M.op x x))
       have r₂ := eq91 x x (M.op (M.op x x) (M.op x x)) X3
       grind)
    | (have r₁ := eq106 x x (M.op x x) (M.op x x)
       have r₂ := eq91 x x (k (M.op x x) (M.op x x)) X3
       grind)
    | exact resolve eq106 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq106
  have eq337 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq112 (σ X1) (σ X0)
       grind)
    | exact superpose eq112 eq15
    | exact resolve eq15 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq337 X0 X1
       have i₂ := eq112 X1 X0
       grind)
    | exact superpose eq112 eq337
    | exact resolve eq337 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq337
  have eq345 : False := by grind
  exact eq345
