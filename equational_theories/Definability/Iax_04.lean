import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation109`: `x = x ◇ ((y ◇ y) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pxx_pxy_Equation109 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law109 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law109.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op (M.op x x) x)
       have i₂ := eq8 (M.op X0 X0) x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X0)
       have i₂ := eq16 X0 (M.op X0 X0)
       grind)
    | exact superpose eq16 eq11
    | (have j0 := eq11 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq16 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq49 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X1 X0
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq56 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq49 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq78 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq121 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 (M.op X1 X1)
       have i₂ := eq29 X1 (σ X0)
       grind)
    | exact superpose eq29 eq78
    | exact resolve eq78 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq432 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (σ X0) X1
       have i₂ := eq53 X2 X0
       grind)
    | exact superpose eq53 eq16
    | (have j1 := eq53 X2 X0
       grind)
    | exact resolve eq16 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1112 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) ≠ (k X0 (M.op X1 X1)) ∨ (k X0 (M.op X1 X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq334 X1 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq334
    | exact resolve eq334 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1127 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq334 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq1129 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1112 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112
  have eq1175 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq1127 (σ X0)
       grind)
    | exact superpose eq1127 eq13
    | exact resolve eq13 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1182 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1175 X0
       have i₂ := eq1127 X0
       grind)
    | exact superpose eq1127 eq1175
    | exact resolve eq1175 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175
  have eq1353 : ∀ X0 X1 : G, (τ (k (σ X0) (M.op X1 X1))) = (k X0 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 (σ X0)
       have i₂ := eq1129 (σ X0) X1
       grind)
    | (have i₁ := eq78 X0 (M.op X1 X1)
       have i₂ := eq1129 (σ X0) X1
       grind)
    | exact superpose eq1129 eq78
    | exact resolve eq78 eq1129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129
  have eq1358 : ∀ X0 X1 : G, (k X0 X0) = (τ (k (σ X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1353 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1353
    | exact resolve eq1353 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1353
  have eq1379 : ∀ X0 X1 : G, (k X0 X0) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1358 X0 X1
       have i₂ := eq78 X0 (M.op X1 X1)
       grind)
    | exact superpose eq78 eq1358
    | exact resolve eq1358 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq1358
  have eq1594 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq54 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq54
    | (have j0 := eq54 X0 X1
       grind)
    | exact resolve eq54 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1703 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1594 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1594
    | (have j0 := eq1594 X0 X1
       grind)
    | exact resolve eq1594 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594
  have eq1884 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 (σ X0) X1
       have i₂ := eq1182 X0
       grind)
    | exact superpose eq1182 eq16
    | exact resolve eq16 eq1182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq9140 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq432 y X0 x
       grind)
    | exact superpose eq432 eq14
    | (have j1 := eq432 y X0 x
       grind)
    | exact resolve eq14 eq432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq105531 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq9140 X0
       have i₂ := eq1703 x y
       grind)
    | exact superpose eq1703 eq9140
    | (have j0 := eq9140 X0
       have j1 := eq1703 X0 y
       grind)
    | (have r₁ := eq9140 X0
       have r₂ := eq1703 x y
       grind)
    | exact resolve eq9140 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1703 eq9140
  have eq105532 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq105531 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105531
  have eq105807 : ∀ X0 : G, (τ (σ y)) = (k y (τ (M.op X0 X0))) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq121 y X0
       have i₂ := eq105532 (σ y)
       grind)
    | exact superpose eq105532 eq121
    | exact resolve eq121 eq105532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq105532
  have eq105862 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq105807 x
       have i₂ := eq1379 y x
       grind)
    | exact superpose eq1379 eq105807
    | exact resolve eq105807 eq1379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1379 eq105807
  have eq105927 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq105862
       have i₂ := eq1127 y
       grind)
    | exact superpose eq1127 eq105862
    | exact resolve eq105862 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127 eq105862
  have eq105940 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq105927
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq105927
    | exact resolve eq105927 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105927
  have eq105941 : y = (M.op y y) := by grind
  clear eq105940
  have eq106195 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 y X0
       have i₂ := eq105941
       grind)
    | exact superpose eq105941 eq16
    | exact resolve eq16 eq105941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq106288 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1884 y X0
       have i₂ := eq105941
       grind)
    | exact superpose eq105941 eq1884
    | exact resolve eq1884 eq105941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1884 eq105941
  have eq111132 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq106288 (σ x)
       grind)
    | exact superpose eq106288 eq14
    | exact resolve eq14 eq106288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106288
  have eq111196 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq111132
       have i₂ := eq106195 x
       grind)
    | exact superpose eq106195 eq111132
    | exact resolve eq111132 eq106195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106195 eq111132
  have eq111197 : False := by grind
  exact eq111197

/-- `Equation109`: `x = x ◇ ((y ◇ y) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pyy_pxy_Equation109 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law109 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law109.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op (M.op x x) x)
       have i₂ := eq8 (M.op X0 X0) x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X0 X0)
       have i₂ := eq16 X0 (M.op X0 X0)
       grind)
    | exact superpose eq16 eq11
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq16 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq41 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq51 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 (M.op X0 X0)
       have i₂ := eq29 X0 (σ X1)
       grind)
    | exact superpose eq29 eq51
    | exact resolve eq51 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq204 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (σ X0) X1
       have i₂ := eq41 X2 X0
       grind)
    | exact superpose eq41 eq16
    | (have j1 := eq41 X2 X0
       grind)
    | exact resolve eq16 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq41 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq649 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq42
    | (have j0 := eq42 X0 X1
       grind)
    | exact resolve eq42 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq705 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq649 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq649
    | (have j0 := eq649 X0 X1
       grind)
    | exact resolve eq649 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq921 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq705 X2 X0
       grind)
    | exact superpose eq705 eq16
    | (have j1 := eq705 X2 X0
       grind)
    | exact resolve eq16 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq1920 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq209 (M.op X0 X0)
       have i₂ := eq29 X0 (M.op X0 X0)
       grind)
    | exact superpose eq29 eq209
    | (have j0 := eq209 (M.op X0 X0)
       grind)
    | exact resolve eq209 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1936 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq209 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq209
    | (have j0 := eq209 (τ X0)
       grind)
    | exact resolve eq209 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq209
  have eq1952 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1920 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1920
  have eq1959 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1936 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1936
    | (have j0 := eq1936 X0
       grind)
    | exact resolve eq1936 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1936
  have eq1968 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1959 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1959
    | (have j0 := eq1959 X0
       grind)
    | exact resolve eq1959 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1959
  have eq2154 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 (σ (M.op X0 X0)) X1
       have i₂ := eq1952 X0
       grind)
    | exact superpose eq1952 eq16
    | exact resolve eq16 eq1952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1952
  have eq2312 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2154 X0 X1
       have i₂ := eq921 X0 X0 X2
       grind)
    | exact superpose eq921 eq2154
    | (have j1 := eq921 (σ X0) X1 X2
       grind)
    | exact resolve eq2154 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921 eq2154
  have eq2790 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq204 y X0 x
       grind)
    | exact superpose eq204 eq14
    | (have j1 := eq204 y X0 x
       grind)
    | exact resolve eq14 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq2828 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq2790 X0
       have j1 := eq2312 y X0 x
       grind)
    | (have r₁ := eq2790 X0
       have r₂ := eq2312 y x x
       grind)
    | exact resolve eq2790 eq2312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2312 eq2790
  have eq2845 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq104 (σ y) x
       have i₂ := eq2828 (σ y)
       grind)
    | exact superpose eq2828 eq104
    | exact resolve eq104 eq2828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq2870 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2828 (σ x)
       grind)
    | exact superpose eq2828 eq14
    | exact resolve eq14 eq2828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2828
  have eq2879 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq2845 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2845
    | exact resolve eq2845 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2845
  have eq2988 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1968 y
       have i₂ := eq2879 y
       grind)
    | exact superpose eq2879 eq1968
    | (have j0 := eq1968 y
       grind)
    | (have r₁ := eq1968 y
       have r₂ := eq2879 y
       grind)
    | exact resolve eq1968 eq2879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1968 eq2879
  have eq3009 : y = (M.op y y) := by grind
  clear eq2988
  have eq3162 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 y X0
       have i₂ := eq3009
       grind)
    | exact superpose eq3009 eq16
    | exact resolve eq16 eq3009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq3009
  have eq3663 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2870
       have i₂ := eq3162 x
       grind)
    | exact superpose eq3162 eq2870
    | exact resolve eq2870 eq3162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2870 eq3162
  have eq3664 : False := by grind
  exact eq3664

/-- `Equation1096`: `x = y ◇ ((x ◇ (z ◇ y)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_y_pyy_pxy_Equation1096 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1096 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1096.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 (M.op X2 X1)) X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X0) (M.op (M.op X3 X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 (M.op (M.op X0 (M.op X1 X2)) X0) X2
       have i₂ := eq8 X0 X2 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op X0 (M.op x X1))
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X1)) X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X1 (M.op (M.op X0 (M.op X2 X1)) X0)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq22
    | exact resolve eq22 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X2 X0) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X1 X0) X1
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = (k (M.op X1 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 X0) X1
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq11
    | (have j0 := eq11 (M.op X1 X0) X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq22 X1 X1
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X2 X3)) (M.op X1 X0)) (M.op X0 X1)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 (M.op X1 X0) X2 X3 X1
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq21
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op X1 (M.op X2 X3)) X1) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 (M.op (M.op X1 (M.op X2 X3)) X1) (M.op (M.op X0 X1) X0)
       have i₂ := eq21 X1 X2 X3 X0
       grind)
    | exact superpose eq21 eq22
    | exact resolve eq22 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq63 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X3 X1) X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq61 X0 X1 x X3
       have i₂ := eq23 X1 X3 x
       grind)
    | exact superpose eq23 eq61
    | exact resolve eq61 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq66 : ∀ X0 X1 X3 : G, (M.op (M.op X3 (M.op X1 X0)) (M.op X0 X1)) = X1 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq57 X0 X1 x X3
       have i₂ := eq23 (M.op X1 X0) X3 x
       grind)
    | exact superpose eq23 eq57
    | exact resolve eq57 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq105 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq38 X1 X0
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq38 X0 X1
       grind)
    | exact resolve eq11 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) (σ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq22
    | (have j1 := eq38 X1 X0
       grind)
    | exact resolve eq22 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq105 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq110 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq109 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq109
    | (have j0 := eq109 X0 X1
       grind)
    | exact resolve eq109 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq201 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X0 (M.op X1 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X3 X2 X1
       have i₂ := eq63 X3 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq23 X0 X1 X2
       have i₂ := eq63 X0 (M.op X2 X1) X0
       grind)
    | exact superpose eq63 eq23
    | exact resolve eq23 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq204 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op (M.op X0 X1) X2)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X1 X3 X2
       have i₂ := eq63 X2 X1 X0
       grind)
    | (have i₁ := eq25 X1 X1 X0
       have i₂ := eq63 X0 X1 X0
       grind)
    | exact superpose eq63 eq25
    | exact resolve eq25 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq291 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq27 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq293 : ∀ X0 : G, (k X0 (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq291 (M.op (M.op x x) x)
       have i₂ := eq25 x (M.op x x) x
       grind)
    | exact superpose eq25 eq291
    | exact resolve eq291 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq291
  have eq321 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X1) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq293 X1
       have i₂ := eq63 X1 X1 X0
       grind)
    | (have i₁ := eq293 X0
       have i₂ := eq63 X0 X0 X0
       grind)
    | exact superpose eq63 eq293
    | exact resolve eq293 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq293
  have eq1306 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq106 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq106
    | exact resolve eq106 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1337 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X0
       have i₂ := eq106 X0 X1
       grind)
    | exact superpose eq106 eq38
    | (have j0 := eq38 X0 X1
       have j1 := eq106 X1 X0
       grind)
    | exact resolve eq38 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1341 : ∀ X0 X1 : G, (σ X0) ≠ (σ X1) ∨ (σ X0) = (k (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X0)
       have i₂ := eq106 X0 X1
       grind)
    | exact superpose eq106 eq11
    | (have j1 := eq106 X1 X0
       grind)
    | (have r₁ := eq11 (σ X1) (σ X1)
       have r₂ := eq106 X1 X1
       grind)
    | exact resolve eq11 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq1401 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ X0) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1341 X0 X1
       have i₂ := eq13 X1 X1
       grind)
    | exact superpose eq13 eq1341
    | (have j0 := eq1341 X0 X1
       grind)
    | exact resolve eq1341 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341
  have eq1406 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1306 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq1306
    | (have j0 := eq1306 X0 X1
       grind)
    | exact resolve eq1306 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306
  have eq1410 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1401 X0 X1
       have j1 := eq1337 X0 X1
       grind)
    | (have r₁ := eq1401 X0 (k X1 X1)
       have r₂ := eq1337 X0 X1
       grind)
    | (have r₁ := eq1401 (k X1 X1) X0
       have r₂ := eq1337 X0 X1
       grind)
    | (have r₁ := eq1401 X0 X1
       have r₂ := eq1337 X0 X1
       grind)
    | exact resolve eq1401 eq1337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337 eq1401
  have eq1603 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op X2 (σ (k X0 X1))) (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 (σ X0) (σ X0) x
       have i₂ := eq110 X0 X1
       grind)
    | exact superpose eq110 eq66
    | (have j1 := eq110 X1 X0
       grind)
    | exact resolve eq66 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq1648 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq110 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq1649 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq1648 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1648
  have eq1800 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1649 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1649
    | exact resolve eq1649 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1814 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0) (σ X0)
       have i₂ := eq1649 X0
       grind)
    | exact superpose eq1649 eq22
    | exact resolve eq22 eq1649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1847 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq1800 X0
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq1800
    | exact resolve eq1800 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq1800
  have eq1850 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1847 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1847
    | exact resolve eq1847 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1847
  have eq2127 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1814 X0
       have i₂ := eq1850 X0
       grind)
    | exact superpose eq1850 eq1814
    | exact resolve eq1814 eq1850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1814
  have eq2535 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (σ X0)) X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq201 X2 (σ X0) (σ (M.op X0 X0)) X1
       have i₂ := eq2127 X0
       grind)
    | exact superpose eq2127 eq201
    | exact resolve eq201 eq2127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq6212 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1406 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1406
    | exact resolve eq1406 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1406
  have eq8666 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq1410 X0 X1
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq1410 X0 X1
       grind)
    | exact superpose eq1410 eq9
    | (have j1 := eq1410 X0 X1
       grind)
    | exact resolve eq9 eq1410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410
  have eq8897 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8666 X0 X1
       have i₂ := eq1850 X1
       grind)
    | exact superpose eq1850 eq8666
    | (have j0 := eq8666 X0 X1
       grind)
    | exact resolve eq8666 eq1850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8666
  have eq9105 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8897 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq8897
    | (have j0 := eq8897 X0 X1
       grind)
    | exact resolve eq8897 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8897
  have eq74349 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq9105 x y
       grind)
    | exact superpose eq9105 eq14
    | (have j1 := eq9105 x y
       grind)
    | exact resolve eq14 eq9105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9105
  have eq78425 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq74349
       have i₂ := eq6212 x y
       grind)
    | exact superpose eq6212 eq74349
    | (have j1 := eq6212 x y
       grind)
    | exact resolve eq74349 eq6212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6212 eq74349
  have eq78435 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by grind
  clear eq78425
  have eq78436 : x = (M.op y y) := by grind
  clear eq78435
  have eq82263 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op X0 (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2535 y X1 X0
       have i₂ := eq78436
       grind)
    | exact superpose eq78436 eq2535
    | exact resolve eq2535 eq78436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2535
  have eq82319 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op x X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq204 y y X1 X0
       have i₂ := eq78436
       grind)
    | exact superpose eq78436 eq204
    | exact resolve eq204 eq78436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq82340 : y = (k y (M.op x y)) := by
    first
    | (have i₁ := eq321 y y
       have i₂ := eq78436
       grind)
    | exact superpose eq78436 eq321
    | exact resolve eq321 eq78436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq91104 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1603 y (M.op x y) x
       have i₂ := eq82340
       grind)
    | exact superpose eq82340 eq1603
    | exact resolve eq1603 eq82340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1603 eq82340
  have eq91294 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq91104 x
       have i₂ := eq82263 x (σ y)
       grind)
    | exact superpose eq82263 eq91104
    | exact resolve eq91104 eq82263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82263 eq91104
  have eq91304 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq91294
       have r₂ := eq14
       grind)
    | exact resolve eq91294 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91294
  have eq99858 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq22 (σ y) (σ (M.op x y))
       have i₂ := eq91304
       grind)
    | exact superpose eq91304 eq22
    | exact resolve eq22 eq91304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq91304
  have eq99934 : (σ (M.op x y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq99858
       have i₂ := eq1649 y
       grind)
    | exact superpose eq1649 eq99858
    | exact resolve eq99858 eq1649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1649 eq99858
  have eq99958 : (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq99934
       have i₂ := eq1850 y
       grind)
    | exact superpose eq1850 eq99934
    | exact resolve eq99934 eq1850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850 eq99934
  have eq99973 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq99958
       have i₂ := eq78436
       grind)
    | exact superpose eq78436 eq99958
    | exact resolve eq99958 eq78436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78436 eq99958
  have eq100308 : (σ x) = (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq2127 (M.op x y)
       have i₂ := eq99973
       grind)
    | exact superpose eq99973 eq2127
    | exact resolve eq2127 eq99973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2127
  have eq100343 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq100308
       have i₂ := eq82319 x y
       grind)
    | exact superpose eq82319 eq100308
    | exact resolve eq100308 eq82319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82319 eq100308
  have eq102702 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq100343
       grind)
    | exact superpose eq100343 eq14
    | exact resolve eq14 eq100343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100343
  have eq102849 : False := by grind
  exact eq102849

/-- `Equation11`: `x = x ◇ (y ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_pxx_pyx_Equation11 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law11 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law11.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 X1) X1
       have i₂ := eq8 (M.op X1 X1) X1
       grind)
    | exact superpose eq8 eq11
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq8 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq18 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq24 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) X1
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq24 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq33 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq35 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (M.op X0 X0)
       have i₂ := eq19 X0 (τ X1)
       grind)
    | exact superpose eq19 eq17
    | exact resolve eq17 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X1 X1
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq28 eq13
    | (have j1 := eq28 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq128 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq26 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq433 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq36 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq36
    | (have j0 := eq36 X0 X1
       grind)
    | exact resolve eq36 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq474 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq433 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq433
    | (have j0 := eq433 X0 X1
       grind)
    | exact resolve eq433 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq804 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X0) X1) ∨ (σ (k X0 X2)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35 X1 X1
       have i₂ := eq474 X0 X1
       grind)
    | exact superpose eq474 eq35
    | (have j1 := eq474 X2 X0
       grind)
    | exact resolve eq35 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq474
  have eq1352 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq128 (M.op X0 X0)
       have i₂ := eq19 X0 (M.op X0 X0)
       grind)
    | exact superpose eq19 eq128
    | (have j0 := eq128 (M.op X0 X0)
       grind)
    | exact resolve eq128 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1365 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq128 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq128
    | (have j0 := eq128 (τ X0)
       grind)
    | exact resolve eq128 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq128
  have eq1376 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1352 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1352
  have eq1382 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1365 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1365
    | (have j0 := eq1365 X0
       grind)
    | exact resolve eq1365 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1365
  have eq1391 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1382 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1382
    | (have j0 := eq1382 X0
       grind)
    | exact resolve eq1382 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1382
  have eq1449 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (σ (M.op X0 X0))
       have i₂ := eq1376 X0
       grind)
    | exact superpose eq1376 eq8
    | exact resolve eq8 eq1376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1376
  have eq2061 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq97 x y X0
       grind)
    | exact superpose eq97 eq14
    | (have j1 := eq97 X0 y X0
       grind)
    | exact resolve eq14 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq2126 : ∀ X0 : G, (σ y) = (k (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq2061 X0
       have j1 := eq804 y X0 x
       grind)
    | (have r₁ := eq2061 X0
       have r₂ := eq804 y x x
       grind)
    | exact resolve eq2061 eq804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804 eq2061
  have eq2170 : ∀ X0 : G, (τ (σ y)) = (k (τ (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq33 (σ y) X0
       have i₂ := eq2126 (σ X0)
       grind)
    | exact superpose eq2126 eq33
    | exact resolve eq33 eq2126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq2126
  have eq2174 : ∀ X0 : G, y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq2170 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2170
    | exact resolve eq2170 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2170
  have eq2316 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1391 y
       have i₂ := eq2174 y
       grind)
    | exact superpose eq2174 eq1391
    | (have j0 := eq1391 y
       grind)
    | (have r₁ := eq1391 y
       have r₂ := eq2174 y
       grind)
    | exact resolve eq1391 eq2174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1391 eq2174
  have eq2332 : y = (M.op y y) := by grind
  clear eq2316
  have eq2440 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 y
       have i₂ := eq2332
       grind)
    | exact superpose eq2332 eq8
    | exact resolve eq8 eq2332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2448 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1449 y X0
       have i₂ := eq2332
       grind)
    | exact superpose eq2332 eq1449
    | exact resolve eq1449 eq2332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449 eq2332
  have eq2756 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2448 (σ x)
       grind)
    | exact superpose eq2448 eq14
    | exact resolve eq14 eq2448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2448
  have eq2764 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2756
       have i₂ := eq2440 x
       grind)
    | exact superpose eq2440 eq2756
    | exact resolve eq2756 eq2440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2440 eq2756
  have eq2765 : False := by grind
  exact eq2765

/-- `Equation11`: `x = x ◇ (y ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pxx_pxy_Equation11 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law11 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law11.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X0)
       have i₂ := eq8 (M.op X0 X0) X0
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 X0 (M.op X1 X1)
       have r₂ := eq8 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq18 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq21 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X1)) = (k X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X2 X0
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X2 (k X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X0 X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op X2 (k X0 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 X0
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X1 X0
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq32 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq51 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq61 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq72 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq33 (σ y) (σ x) X0
       grind)
    | exact superpose eq33 eq14
    | (have j1 := eq33 (σ y) x X0
       grind)
    | exact resolve eq14 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq33 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq33 eq13
    | (have j1 := eq33 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq124 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq36 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq130 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 (M.op X1 X1)
       have i₂ := eq19 X1 (σ X0)
       grind)
    | exact superpose eq19 eq61
    | exact resolve eq61 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 X1 X2 X3 : G, (k X2 (k X0 (M.op X1 X1))) = (k X2 (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X2 X3 (k X0 (M.op X1 X1))
       have i₂ := eq25 X0 X1 (k X0 (M.op X1 X1))
       grind)
    | exact superpose eq25 eq21
    | exact resolve eq21 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 X1 X2 X3 X4 : G, (k X0 (k X1 (M.op X2 X2))) = (k X0 (k X3 (M.op X4 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq23 X3 X4 X0
       have i₂ := eq23 X1 X2 X0
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (k X4 (k X0 (k X1 (M.op X2 X2))))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq25 X4 X0 X3
       have i₂ := eq23 X1 X2 X0
       grind)
    | exact superpose eq23 eq25
    | exact resolve eq25 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq25
  have eq710 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) ≠ (k X0 (M.op X1 X1)) ∨ (k X0 (M.op X1 X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq124 X1 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq124
    | exact resolve eq124 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq717 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq124 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq719 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq710 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq751 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq717 (σ X0)
       grind)
    | exact superpose eq717 eq13
    | exact resolve eq13 eq717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq758 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq751 X0
       have i₂ := eq717 X0
       grind)
    | exact superpose eq717 eq751
    | exact resolve eq751 eq717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq886 : ∀ X0 X1 : G, (τ (k (σ X0) (M.op X1 X1))) = (k X0 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 (σ X0)
       have i₂ := eq719 (σ X0) X1
       grind)
    | (have i₁ := eq61 X0 (M.op X1 X1)
       have i₂ := eq719 (σ X0) X1
       grind)
    | exact superpose eq719 eq61
    | exact resolve eq61 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq891 : ∀ X0 X1 : G, (k X0 X0) = (τ (k (σ X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq886 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq886
    | exact resolve eq886 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq911 : ∀ X0 X1 : G, (k X0 X0) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq891 X0 X1
       have i₂ := eq61 X0 (M.op X1 X1)
       grind)
    | exact superpose eq61 eq891
    | exact resolve eq891 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq891
  have eq916 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq51 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1006 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq916 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq916
    | (have j0 := eq916 X0 X1
       grind)
    | exact resolve eq916 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq1474 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (σ X0)
       have i₂ := eq758 X0
       grind)
    | exact superpose eq758 eq8
    | exact resolve eq8 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1480 : ∀ X0 X1 X2 : G, (k X1 (M.op X2 X2)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X1 X2 (σ X0)
       have i₂ := eq758 X0
       grind)
    | exact superpose eq758 eq21
    | exact resolve eq21 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq758
  have eq2575 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq73 x y X0
       grind)
    | exact superpose eq73 eq14
    | (have j1 := eq73 X0 y X0
       grind)
    | exact resolve eq14 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq55710 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq2575 X0
       have i₂ := eq1006 x y
       grind)
    | exact superpose eq1006 eq2575
    | (have j0 := eq2575 X0
       have j1 := eq1006 X0 y
       grind)
    | (have r₁ := eq2575 X0
       have r₂ := eq1006 x y
       grind)
    | exact resolve eq2575 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006 eq2575
  have eq55711 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq55710 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55710
  have eq55855 : ∀ X0 : G, (τ (σ y)) = (k y (τ (M.op X0 X0))) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq130 y X0
       have i₂ := eq55711 (σ y)
       grind)
    | exact superpose eq55711 eq130
    | exact resolve eq130 eq55711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq55711
  have eq55867 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq55855 x
       have i₂ := eq911 y x
       grind)
    | exact superpose eq911 eq55855
    | exact resolve eq55855 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911 eq55855
  have eq55930 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq55867
       have i₂ := eq717 y
       grind)
    | exact superpose eq717 eq55867
    | exact resolve eq55867 eq717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717 eq55867
  have eq55946 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq55930
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq55930
    | exact resolve eq55930 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55930
  have eq55947 : y = (M.op y y) := by grind
  clear eq55946
  have eq56169 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 y
       have i₂ := eq55947
       grind)
    | exact superpose eq55947 eq8
    | exact resolve eq8 eq55947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56191 : ∀ X0 X1 X2 : G, (k X0 (M.op X2 X2)) = (k X0 (k X1 y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq216 X1 y X0 X2
       have i₂ := eq55947
       grind)
    | exact superpose eq55947 eq216
    | exact resolve eq216 eq55947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq56245 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1474 y X0
       have i₂ := eq55947
       grind)
    | exact superpose eq55947 eq1474
    | exact resolve eq1474 eq55947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474
  have eq56246 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = (k X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1480 y X0 X1
       have i₂ := eq55947
       grind)
    | exact superpose eq55947 eq1480
    | exact resolve eq1480 eq55947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1480 eq55947
  have eq56309 : ∀ X0 X1 : G, (k X0 (σ y)) = (k X0 (k X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq56191 X0 X1 x
       have i₂ := eq56246 X0 x
       grind)
    | exact superpose eq56246 eq56191
    | exact resolve eq56191 eq56246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56191
  have eq57229 : ∀ X0 X1 X2 X3 : G, (k X0 (k X1 (M.op X2 X2))) = (k X0 (k X3 y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq246 X0 X1 X2 X3 y
       have i₂ := eq56169 y
       grind)
    | exact superpose eq56169 eq246
    | exact resolve eq246 eq56169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq57322 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq72 X0
       have i₂ := eq56169 x
       grind)
    | exact superpose eq56169 eq72
    | (have j0 := eq72 X0
       grind)
    | exact resolve eq72 eq56169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq57323 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq57322 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57322
  have eq57327 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq57323 X0
       have i₂ := eq56245 X0
       grind)
    | exact superpose eq56245 eq57323
    | exact resolve eq57323 eq56245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56245 eq57323
  have eq57345 : ∀ X0 X1 X2 : G, (k X0 (k X1 (M.op X2 X2))) = (k X0 (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57229 X0 X1 X2 x
       have i₂ := eq56309 X0 x
       grind)
    | exact superpose eq56309 eq57229
    | exact resolve eq57229 eq56309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56309 eq57229
  have eq57364 : ∀ X0 X1 X2 : G, (k X0 (k X1 (M.op X2 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57345 X0 X1 X2
       have i₂ := eq57327 X0
       grind)
    | exact superpose eq57327 eq57345
    | exact resolve eq57345 eq57327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57345
  have eq57375 : ∀ X0 X1 : G, (k X0 (k X1 (σ y))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq57364 X0 X1 x
       have i₂ := eq56246 X1 x
       grind)
    | exact superpose eq56246 eq57364
    | exact resolve eq57364 eq56246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56246 eq57364
  have eq57379 : ∀ X0 X1 : G, (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq57375 X0 X1
       have i₂ := eq57327 X1
       grind)
    | exact superpose eq57327 eq57375
    | exact resolve eq57375 eq57327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57327 eq57375
  have eq58522 : ∀ X0 X1 : G, (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq281 x x x X1 X0
       have i₂ := eq57379 X0 (k x (k x (M.op x x)))
       grind)
    | exact superpose eq57379 eq281
    | exact resolve eq281 eq57379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq57379
  have eq59180 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq58522 (σ y) (σ x)
       grind)
    | exact superpose eq58522 eq14
    | exact resolve eq14 eq58522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58522
  have eq59220 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq59180
       have i₂ := eq56169 x
       grind)
    | exact superpose eq56169 eq59180
    | exact resolve eq59180 eq56169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56169 eq59180
  have eq59221 : False := by grind
  exact eq59221

/-- `Equation11`: `x = x ◇ (y ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pyy_pxy_Equation11 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law11 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law11.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X1 X1)
       have i₂ := eq8 (M.op X1 X1) X1
       grind)
    | exact superpose eq8 eq11
    | (have r₁ := eq11 X0 (M.op X1 X1)
       have r₂ := eq8 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq18 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq24 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq24 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq30 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0)
       have i₂ := eq19 X0 (τ X1)
       grind)
    | exact superpose eq19 eq16
    | exact resolve eq16 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq41 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq28 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq28 eq13
    | (have j1 := eq28 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq128 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq26 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq250 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq31
    | (have j0 := eq31 X0 X1
       grind)
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq285 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq250 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq250
    | (have j0 := eq250 X0 X1
       grind)
    | exact resolve eq250 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq803 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X1 X1
       have i₂ := eq285 X0 X1
       grind)
    | exact superpose eq285 eq30
    | (have j1 := eq285 X2 X0
       grind)
    | exact resolve eq30 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq285
  have eq1350 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq128 (M.op X0 X0)
       have i₂ := eq19 X0 (M.op X0 X0)
       grind)
    | exact superpose eq19 eq128
    | (have j0 := eq128 (M.op X0 X0)
       grind)
    | exact resolve eq128 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1364 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq128 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq128
    | (have j0 := eq128 (τ X0)
       grind)
    | exact resolve eq128 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq128
  have eq1376 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1350 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1350
  have eq1381 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1364 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1364
    | (have j0 := eq1364 X0
       grind)
    | exact resolve eq1364 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1364
  have eq1390 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1381 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1381
    | (have j0 := eq1381 X0
       grind)
    | exact resolve eq1381 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381
  have eq1448 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (σ (M.op X0 X0))
       have i₂ := eq1376 X0
       grind)
    | exact superpose eq1376 eq8
    | exact resolve eq8 eq1376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1376
  have eq2060 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq94 x y X0
       grind)
    | exact superpose eq94 eq14
    | (have j1 := eq94 X0 y X0
       grind)
    | exact resolve eq14 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq2125 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq2060 X0
       have j1 := eq803 y X0 x
       grind)
    | (have r₁ := eq2060 X0
       have r₂ := eq803 y x x
       grind)
    | exact resolve eq2060 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803 eq2060
  have eq2167 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq41 X0 (σ y)
       have i₂ := eq2125 (σ X0)
       grind)
    | exact superpose eq2125 eq41
    | exact resolve eq41 eq2125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq2125
  have eq2173 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq2167 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2167
    | exact resolve eq2167 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2167
  have eq2315 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1390 y
       have i₂ := eq2173 y
       grind)
    | exact superpose eq2173 eq1390
    | (have j0 := eq1390 y
       grind)
    | (have r₁ := eq1390 y
       have r₂ := eq2173 y
       grind)
    | exact resolve eq1390 eq2173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390 eq2173
  have eq2331 : y = (M.op y y) := by grind
  clear eq2315
  have eq2437 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 y
       have i₂ := eq2331
       grind)
    | exact superpose eq2331 eq8
    | exact resolve eq8 eq2331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2445 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1448 y X0
       have i₂ := eq2331
       grind)
    | exact superpose eq2331 eq1448
    | exact resolve eq1448 eq2331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448 eq2331
  have eq2763 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2445 (σ x)
       grind)
    | exact superpose eq2445 eq14
    | exact resolve eq14 eq2445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2445
  have eq2771 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2763
       have i₂ := eq2437 x
       grind)
    | exact superpose eq2437 eq2763
    | exact resolve eq2763 eq2437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2437 eq2763
  have eq2772 : False := by grind
  exact eq2772

/-- `Equation111`: `x = x ◇ ((y ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pxx_pxy_Equation111 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law111 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law111.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) X1)) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op (M.op x x) x)
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X0)
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq11
    | (have j0 := eq11 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq60 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X1 X0
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq60 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq87 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq97 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq183 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (M.op X1 X1)
       have i₂ := eq36 X1 (σ X0)
       grind)
    | exact superpose eq36 eq97
    | exact resolve eq97 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq66 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq290 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (σ X0) X1
       have i₂ := eq64 X2 X0
       grind)
    | exact superpose eq64 eq15
    | (have j1 := eq64 X2 X0
       grind)
    | exact resolve eq15 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq908 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) ≠ (k X0 (M.op X1 X1)) ∨ (k X0 (M.op X1 X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq243 X1 X1
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq243
    | exact resolve eq243 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq920 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq243 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq922 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq908 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq957 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq920 (σ X0)
       grind)
    | exact superpose eq920 eq13
    | exact resolve eq13 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq964 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq957 X0
       have i₂ := eq920 X0
       grind)
    | exact superpose eq920 eq957
    | exact resolve eq957 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq1110 : ∀ X0 X1 : G, (τ (k (σ X0) (M.op X1 X1))) = (k X0 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (σ X0)
       have i₂ := eq922 (σ X0) X1
       grind)
    | (have i₁ := eq97 X0 (M.op X1 X1)
       have i₂ := eq922 (σ X0) X1
       grind)
    | exact superpose eq922 eq97
    | exact resolve eq97 eq922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq1115 : ∀ X0 X1 : G, (k X0 X0) = (τ (k (σ X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1110 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1110
    | exact resolve eq1110 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq1131 : ∀ X0 X1 : G, (k X0 X0) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1115 X0 X1
       have i₂ := eq97 X0 (M.op X1 X1)
       grind)
    | exact superpose eq97 eq1115
    | exact resolve eq1115 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq1115
  have eq1136 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq87 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq87
    | (have j0 := eq87 X0 X1
       grind)
    | exact resolve eq87 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq1224 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1136 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1136
    | (have j0 := eq1136 X0 X1
       grind)
    | exact resolve eq1136 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136
  have eq1613 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 (σ X0) X1
       have i₂ := eq964 X0
       grind)
    | exact superpose eq964 eq15
    | exact resolve eq15 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964
  have eq6533 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq290 y X0 x
       grind)
    | exact superpose eq290 eq14
    | (have j1 := eq290 y X0 x
       grind)
    | exact resolve eq14 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq89700 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq6533 X0
       have i₂ := eq1224 x y
       grind)
    | exact superpose eq1224 eq6533
    | (have j0 := eq6533 X0
       have j1 := eq1224 X0 y
       grind)
    | (have r₁ := eq6533 X0
       have r₂ := eq1224 x y
       grind)
    | exact resolve eq6533 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224 eq6533
  have eq89701 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq89700 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89700
  have eq89993 : ∀ X0 : G, (τ (σ y)) = (k y (τ (M.op X0 X0))) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq183 y X0
       have i₂ := eq89701 (σ y)
       grind)
    | exact superpose eq89701 eq183
    | exact resolve eq183 eq89701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq89701
  have eq90037 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq89993 x
       have i₂ := eq1131 y x
       grind)
    | exact superpose eq1131 eq89993
    | exact resolve eq89993 eq1131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131 eq89993
  have eq90102 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq90037
       have i₂ := eq920 y
       grind)
    | exact superpose eq920 eq90037
    | exact resolve eq90037 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920 eq90037
  have eq90113 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq90102
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq90102
    | exact resolve eq90102 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90102
  have eq90114 : y = (M.op y y) := by grind
  clear eq90113
  have eq90355 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq90114
       grind)
    | exact superpose eq90114 eq15
    | exact resolve eq15 eq90114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq90422 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1613 y X0
       have i₂ := eq90114
       grind)
    | exact superpose eq90114 eq1613
    | exact resolve eq1613 eq90114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1613 eq90114
  have eq95377 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq90422 (σ x)
       grind)
    | exact superpose eq90422 eq14
    | exact resolve eq14 eq90422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90422
  have eq95430 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq95377
       have i₂ := eq90355 x
       grind)
    | exact superpose eq90355 eq95377
    | exact resolve eq95377 eq90355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90355 eq95377
  have eq95431 : False := by grind
  exact eq95431

/-- `Equation111`: `x = x ◇ ((y ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pyy_pxy_Equation111 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law111 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law111.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) X1)) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op (M.op x x) x)
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X0 X0)
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq11
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq49 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq64 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1 (M.op X0 X0)
       have i₂ := eq36 X0 (σ X1)
       grind)
    | exact superpose eq36 eq64
    | exact resolve eq64 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq196 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (σ X0) X1
       have i₂ := eq49 X2 X0
       grind)
    | exact superpose eq49 eq15
    | (have j1 := eq49 X2 X0
       grind)
    | exact resolve eq15 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq49 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq439 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq54 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq54
    | (have j0 := eq54 X0 X1
       grind)
    | exact resolve eq54 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq490 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq439 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq439
    | (have j0 := eq439 X0 X1
       grind)
    | exact resolve eq439 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq1716 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq197 (M.op X0 X0)
       have i₂ := eq36 X0 (M.op X0 X0)
       grind)
    | exact superpose eq36 eq197
    | (have j0 := eq197 (M.op X0 X0)
       grind)
    | exact resolve eq197 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1732 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq197 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq197
    | (have j0 := eq197 (τ X0)
       grind)
    | exact resolve eq197 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq197
  have eq1747 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1716 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1716
  have eq1752 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1732 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1732
    | (have j0 := eq1732 X0
       grind)
    | exact resolve eq1732 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1732
  have eq1761 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1752 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1752
    | (have j0 := eq1752 X0
       grind)
    | exact resolve eq1752 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1752
  have eq1957 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 (σ (M.op X0 X0)) X1
       have i₂ := eq1747 X0
       grind)
    | exact superpose eq1747 eq15
    | exact resolve eq15 eq1747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1747
  have eq2062 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1957 X0 X1
       have i₂ := eq490 X2 X0
       grind)
    | exact superpose eq490 eq1957
    | (have j1 := eq490 X2 X0
       grind)
    | exact resolve eq1957 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490 eq1957
  have eq2212 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq196 y X0 x
       grind)
    | exact superpose eq196 eq14
    | (have j1 := eq196 y X0 x
       grind)
    | exact resolve eq14 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq2247 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq2212 X0
       have j1 := eq2062 y X0 x
       grind)
    | (have r₁ := eq2212 X0
       have r₂ := eq2062 y x x
       grind)
    | exact resolve eq2212 eq2062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2062 eq2212
  have eq2263 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq102 (σ y) x
       have i₂ := eq2247 (σ y)
       grind)
    | exact superpose eq2247 eq102
    | exact resolve eq102 eq2247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq2295 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2247 (σ x)
       grind)
    | exact superpose eq2247 eq14
    | exact resolve eq14 eq2247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2247
  have eq2303 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq2263 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2263
    | exact resolve eq2263 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2263
  have eq2393 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1761 y
       have i₂ := eq2303 y
       grind)
    | exact superpose eq2303 eq1761
    | (have j0 := eq1761 y
       grind)
    | (have r₁ := eq1761 y
       have r₂ := eq2303 y
       grind)
    | exact resolve eq1761 eq2303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1761 eq2303
  have eq2409 : y = (M.op y y) := by grind
  clear eq2393
  have eq2535 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq2409
       grind)
    | exact superpose eq2409 eq15
    | exact resolve eq15 eq2409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq2409
  have eq3018 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2295
       have i₂ := eq2535 x
       grind)
    | exact superpose eq2535 eq2295
    | exact resolve eq2295 eq2535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2295 eq2535
  have eq3019 : False := by grind
  exact eq3019
