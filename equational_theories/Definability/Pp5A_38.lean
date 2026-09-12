import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4401`: `x ◇ (x ◇ y) = (x ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(X,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_pyx_pxx_pyx_Equation4401 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4401 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4401.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X0) := by
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
  have eq52 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 X0 x X3
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op (M.op x y) x) := by
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
  have eq56 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 X2) ∨ (M.op X0 (M.op X0 X2)) = (k (M.op X0 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X0 X2) X0
       grind)
    | (have r₁ := eq13 (M.op X0 (M.op X0 X1)) X0
       have r₂ := eq14 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : x ≠ (M.op x y) ∨ (k x y) = (M.op y x) := by
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
  have eq70 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq78 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq80 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq78
       grind)
    | exact superpose eq78 eq16
    | exact resolve eq16 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq80 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq80
    | (have j0 := eq80 (σ X0) (σ X1)
       grind)
    | exact resolve eq80 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq77
       have i₂ := eq80 y x
       grind)
    | exact superpose eq80 eq77
    | (have j1 := eq80 y x
       grind)
    | exact resolve eq77 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
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
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq133 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq134 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq135 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq169 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq135 eq16
    | exact resolve eq16 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq210 : (M.op (M.op x y) x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq55 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55
    | (have j0 := eq55 y
       grind)
    | exact resolve eq55 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq56
    | (have j0 := eq56 (σ y)
       grind)
    | exact resolve eq56 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq56 x
       have i₂ := eq14 sF2 x x
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq371 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq220 eq223
    | exact resolve eq223 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq223
  have eq945 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq114 eq80
    | (have j0 := eq80 (σ y) (σ x)
       grind)
    | exact resolve eq80 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq946 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq945
    | exact resolve eq945 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq949 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq946
       have r₂ := eq27
       grind)
    | exact resolve eq946 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq953 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq949 eq14
    | exact resolve eq14 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq967 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq953
    | (have j0 := eq953 X0
       grind)
    | exact resolve eq953 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953
  have eq1018 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq96 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq1063 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq949 eq967
    | exact resolve eq967 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967
  have eq1094 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq1063
  have eq1240 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1094 eq949
    | exact resolve eq949 eq1094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1256 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1240
  have eq1261 : ∀ X0 : G, (M.op x y) = (M.op y (M.op y X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq1256
       grind)
    | exact superpose eq1256 eq14
    | exact resolve eq14 eq1256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1277 : ∀ X0 : G, (M.op x y) = (M.op y (M.op y X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1261 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1261
    | (have j0 := eq1261 X0
       grind)
    | exact resolve eq1261 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261
  have eq1459 : (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1277 x
       have i₂ := eq1256
       grind)
    | exact superpose eq1256 eq1277
    | exact resolve eq1277 eq1256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1460 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1277 (M.op y x)
       have i₂ := eq1277 x
       grind)
    | exact superpose eq1277 eq1277
    | exact resolve eq1277 eq1277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1495 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1460
  have eq1496 : (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1459
  have eq1547 : ∀ X0 : G, (M.op x (M.op x X0)) ≠ (M.op (M.op x y) x) ∨ (M.op x (M.op (M.op x y) x)) = (k (M.op (M.op x y) x) x) := by
    intro X0
    first
    | (have i₁ := eq68 x x (M.op x X0)
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq68
    | exact resolve eq68 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1548 : ∀ X0 : G, (M.op x y) ≠ (M.op y (M.op y X0)) ∨ (M.op y (M.op x y)) = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq68 y x (M.op y X0)
       have i₂ := eq1277 X0
       grind)
    | exact superpose eq1277 eq68
    | exact resolve eq68 eq1277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq1554 : (M.op y (M.op x y)) = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1548 x
       have r₂ := eq1277 x
       grind)
    | exact resolve eq1548 eq1277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277 eq1548
  have eq1555 : (M.op x (M.op (M.op x y) x)) = (k (M.op (M.op x y) x) x) := by
    first
    | (have r₁ := eq1547 x
       have r₂ := eq55 x
       grind)
    | exact resolve eq1547 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1547
  have eq1569 : (M.op x (M.op x (M.op x y))) = (k (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq210 eq1555
    | exact resolve eq1555 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1555
  have eq1575 : (M.op (M.op x y) x) = (k (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq1569
       have i₂ := eq55 sF0
       grind)
    | exact superpose eq55 eq1569
    | exact resolve eq1569 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq1569
  have eq1579 : (M.op x (M.op x y)) = (k (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq210 eq1575
    | exact resolve eq1575 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1575
  have eq1614 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1256
       have i₂ := eq1496
       grind)
    | exact superpose eq1496 eq1256
    | exact resolve eq1256 eq1496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256 eq1496
  have eq1633 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1614
  have eq1723 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1633 eq27
    | exact resolve eq27 eq1633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1724 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1633 eq70
    | (have r₁ := eq70
       have r₂ := eq1633
       grind)
    | exact resolve eq70 eq1633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq1633
  have eq1727 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1724
  have eq1789 : (k (σ (M.op x y)) (σ y)) = (σ (M.op y (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1554 eq134
    | exact resolve eq134 eq1554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq1554
  have eq1795 : (k x y) = (τ (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1727 eq61
    | exact resolve eq61 eq1727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq1727
  have eq1800 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1495 eq1789
    | exact resolve eq1789 eq1495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1495 eq1789
  have eq1814 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1800
  have eq1816 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1814
    | exact resolve eq1814 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1814
  have eq1817 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1816
       have i₂ := eq80 sF1 sF3
       grind)
    | exact superpose eq80 eq1816
    | (have j1 := eq80 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq1816 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1816
  have eq1831 : (τ (σ x)) = (k x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq949 eq1795
    | exact resolve eq1795 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1795
  have eq1845 : x = (k x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28 eq1831
    | exact resolve eq1831 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1831
  have eq4791 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq80 x y
       have i₂ := eq1845
       grind)
    | exact superpose eq1845 eq80
    | (have j0 := eq80 y x
       grind)
    | exact resolve eq80 eq1845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1845
  have eq4792 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq4791
  have eq4794 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4792
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4792
    | exact resolve eq4792 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4792
  have eq4814 : ∀ X0 : G, (M.op x y) = (M.op y (M.op y X0)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq4794
       grind)
    | exact superpose eq4794 eq14
    | exact resolve eq14 eq4794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4843 : ∀ X0 : G, (M.op x y) = (M.op y (M.op y X0)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4814 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4814
    | (have j0 := eq4814 X0
       grind)
    | exact resolve eq4814 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4814
  have eq5415 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4843 x
       have i₂ := eq4794
       grind)
    | exact superpose eq4794 eq4843
    | exact resolve eq4843 eq4794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4843
  have eq5500 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5415
  have eq5938 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4794
       have i₂ := eq5500
       grind)
    | exact superpose eq5500 eq4794
    | exact resolve eq4794 eq5500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4794 eq5500
  have eq5973 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5938
  have eq5977 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5973 eq20
    | exact resolve eq20 eq5973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5986 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5973 eq210
    | exact resolve eq210 eq5973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq5997 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5973 eq1579
    | exact resolve eq1579 eq5973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1579
  have eq6035 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5997
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5997
    | exact resolve eq5997 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5997
  have eq6043 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5986
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5986
    | exact resolve eq5986 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5986
  have eq6051 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5977
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5977
    | exact resolve eq5977 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5977
  have eq6359 : (k y y) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6051 eq90
    | exact resolve eq90 eq6051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq6389 : (k y y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq169 eq6359
    | exact resolve eq6359 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6359
  have eq6397 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6035 eq133
    | exact resolve eq133 eq6035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq6035
  have eq6400 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq6397
    | exact resolve eq6397 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6397
  have eq6419 : y ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq6043
       grind)
    | exact superpose eq6043 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq6043
       grind)
    | exact resolve eq13 eq6043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6043
  have eq6446 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq6419
       have r₂ := eq5973
       grind)
    | exact resolve eq6419 eq5973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5973 eq6419
  have eq6447 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6446
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6446
    | exact resolve eq6446 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq6446
  have eq6516 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77
       have i₂ := eq6447
       grind)
    | exact superpose eq6447 eq77
    | exact resolve eq77 eq6447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq6447
  have eq6520 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq6516
    | exact resolve eq6516 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6516
  have eq6536 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6520 eq80
    | (have j0 := eq80 (σ y) (σ x)
       grind)
    | exact resolve eq80 eq6520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq6520
  have eq6540 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq6536
    | exact resolve eq6536 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6536
  have eq6543 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq6540
       have r₂ := eq27
       grind)
    | exact resolve eq6540 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6540
  have eq6545 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6051 eq6543
    | exact resolve eq6543 eq6051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6558 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6543 eq52
    | exact resolve eq52 eq6543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq6543
  have eq6576 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq6545
  have eq6587 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq6558
    | (have j0 := eq6558 X0
       grind)
    | exact resolve eq6558 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6558
  have eq6930 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6576 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) (σ x)
       have r₂ := eq6576
       grind)
    | exact resolve eq12 eq6576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6576
  have eq6954 : (σ (M.op x y)) = (σ x) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq6930
  have eq6957 : (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq6954
       have r₂ := eq1723
       grind)
    | exact resolve eq6954 eq1723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1723 eq6954
  have eq9885 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6957 eq6400
    | exact resolve eq6400 eq6957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6400 eq6957
  have eq9888 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq9885
  have eq9966 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9888 eq13
    | (have r₁ := eq13 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq9888
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq9888
       grind)
    | exact resolve eq13 eq9888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9888
  have eq9994 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq9966
  have eq10408 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9994 eq169
    | exact resolve eq169 eq9994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169 eq9994
  have eq10414 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq10408
    | exact resolve eq10408 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq10408
  have eq10845 : (M.op x y) = (k y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10414 eq6389
    | exact resolve eq6389 eq10414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6389 eq10414
  have eq10857 : (M.op x y) = (k y y) ∨ x = (M.op x y) := by grind
  clear eq10845
  have eq11790 : (σ y) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1018 y
       have i₂ := eq10857
       grind)
    | exact superpose eq10857 eq1018
    | (have j0 := eq1018 y
       grind)
    | exact resolve eq1018 eq10857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018 eq10857
  have eq11792 : (σ y) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq11790
    | exact resolve eq11790 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11790
  have eq11794 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11792
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11792
    | exact resolve eq11792 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11792
  have eq11795 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11794
       have r₂ := eq6051
       grind)
    | exact resolve eq11794 eq6051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11794
  have eq11796 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11795
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11795
    | exact resolve eq11795 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq11795
  have eq13210 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11796 eq6587
    | exact resolve eq6587 eq11796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6587
  have eq13247 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13210
  have eq13519 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13247 eq11796
    | exact resolve eq11796 eq13247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11796 eq13247
  have eq13561 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13519
  have eq13566 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13561 eq27
    | exact resolve eq27 eq13561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13561
  have eq13603 : x = (M.op x y) := by
    first
    | (have r₁ := eq13566
       have r₂ := eq6051
       grind)
    | exact resolve eq13566 eq6051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6051 eq13566
  have eq13611 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq13603 eq20
    | exact resolve eq20 eq13603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq13613 : x ≠ x ∨ (k x y) = (M.op y x) := by
    first
    | exact superpose eq13603 eq69
    | (have r₁ := eq69
       have r₂ := eq13603
       grind)
    | exact resolve eq69 eq13603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq13603
  have eq13663 : (k x y) = (M.op y x) := by grind
  clear eq13613
  have eq13696 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13611
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13611
    | exact resolve eq13611 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13611
  have eq13708 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq13696 eq26
    | exact resolve eq26 eq13696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq13722 : ∀ X0 : G, (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq13696 eq371
    | exact resolve eq371 eq13696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq13724 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq13696 eq949
    | exact resolve eq949 eq13696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq13725 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq13696 eq1094
    | exact resolve eq1094 eq13696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094
  have eq13772 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq13708 eq1817
    | exact resolve eq1817 eq13708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1817
  have eq13773 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq13708 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq13708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13808 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq13773
       have r₂ := eq27
       grind)
    | exact resolve eq13773 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13773
  have eq13809 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq13696 eq13772
    | exact resolve eq13772 eq13696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13772
  have eq13813 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq13809
       have r₂ := eq27
       grind)
    | exact resolve eq13809 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13809
  have eq14780 : (k (σ x) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq13663
       grind)
    | exact superpose eq13663 eq44
    | exact resolve eq44 eq13663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq13663
  have eq14783 : (σ (M.op y x)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq13696 eq14780
    | exact resolve eq14780 eq13696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14780
  have eq17585 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq13813 eq14
    | exact resolve eq14 eq13813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17650 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq13708 eq17585
    | exact resolve eq17585 eq13708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17585
  have eq28081 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq13725 eq13724
    | exact resolve eq13724 eq13725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13724 eq13725
  have eq28151 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq28081
  have eq28155 : x = (M.op y x) := by
    first
    | (have r₁ := eq28151
       have r₂ := eq27
       grind)
    | exact resolve eq28151 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28151
  have eq28167 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq14783
       have i₂ := eq28155
       grind)
    | exact superpose eq28155 eq14783
    | exact resolve eq14783 eq28155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14783 eq28155
  have eq28307 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq28167
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28167
    | exact resolve eq28167 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq28167
  have eq28352 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq13696 eq28307
    | exact resolve eq28307 eq13696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13696 eq28307
  have eq38146 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq28352 eq13808
    | exact resolve eq13808 eq28352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13808 eq28352
  have eq39701 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13813 eq17650
    | exact resolve eq17650 eq13813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17650
  have eq39872 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq39701
  have eq39961 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39872 eq13813
    | exact resolve eq13813 eq39872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13813 eq39872
  have eq40050 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq39961
  have eq40052 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq40050
       have r₂ := eq27
       grind)
    | exact resolve eq40050 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40050
  have eq40082 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq40052 eq38146
    | (have r₁ := eq38146
       have r₂ := eq40052
       grind)
    | exact resolve eq38146 eq40052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38146
  have eq40083 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq40082
  have eq40129 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq40083 eq13722
    | exact resolve eq13722 eq40083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13722
  have eq40236 : (M.op (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq40052 eq40129
    | exact resolve eq40129 eq40052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40052 eq40129
  have eq40265 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq40083 eq40236
    | exact resolve eq40236 eq40083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40083 eq40236
  have eq40291 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13708 eq40265
    | exact resolve eq40265 eq13708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13708 eq40265
  have eq40317 : False := by grind
  exact eq40317

/-- `Equation4404`: `x ◇ (x ◇ y) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_y_x_pxx_pyx_Equation4404 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4404 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4404.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X3) := by
    intro X0 X1 X2 X3
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
  have eq176 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X4) X5) = (M.op X0 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 X0 (M.op X0 x) X4 X5
       have i₂ := eq16 X0 x X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op (M.op X0 X2) X4) X5) = (M.op (M.op X0 X2) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 (M.op X0 X2) x X4 X5
       have i₂ := eq16 X0 X1 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X5) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 X0 x X4 X5
       have i₂ := eq16 X0 x X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (M.op x (M.op x X0)) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x X0 y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 y X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y) X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x x
       have i₂ := eq16 X0 X2 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 X4)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X0 X4 X1 (M.op (M.op X0 X1) x)
       have i₂ := eq16 (M.op X0 X1) x X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ X3 ∨ (M.op X0 X2) = (k (M.op X0 X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X0 X2) X3
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 (M.op X0 X2) X3
       grind)
    | (have r₁ := eq13 (M.op X0 X2) (M.op X0 (M.op X0 X1))
       have r₂ := eq16 X0 X1 X2 (M.op X0 (M.op X0 X1))
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq182 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq182
    | (have j0 := eq182 y X0
       grind)
    | exact resolve eq182 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X2 X3 : G, (M.op (M.op x y) X0) = (M.op (M.op x X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq16 x x X2 X3
       have i₂ := eq182 x X0
       grind)
    | exact superpose eq182 eq16
    | exact resolve eq16 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq209 : ∀ X0 : G, (M.op x (M.op x y)) ≠ X0 ∨ (M.op x y) = (k (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq188 eq13
    | (have j0 := eq13 (M.op x y) X0
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op x (M.op x y))
       have r₂ := eq188 (M.op x (M.op x y))
       grind)
    | exact resolve eq13 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq183
    | (have j0 := eq183 (σ y) X0
       grind)
    | exact resolve eq183 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : ∀ X0 X2 : G, (M.op (M.op (σ x) (σ y)) X2) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X2
    first
    | exact superpose eq183 eq183
    | exact resolve eq183 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : ∀ X0 X2 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) (σ y)) X2) := by
    intro X0 X2
    first
    | exact superpose eq183 eq183
    | exact resolve eq183 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 X2 X3 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) X2) X3) := by
    intro X0 X2 X3
    first
    | exact superpose eq183 eq16
    | exact resolve eq16 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq367 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq195 eq188
    | exact resolve eq188 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq441 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq244 eq237
    | exact resolve eq237 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq687 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
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
  have eq699 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq745 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (k (M.op (M.op (σ x) (σ y)) X0) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) ∨ (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq238 X0 x
       have i₂ := eq11 (M.op sF4 X0) sF2
       grind)
    | exact superpose eq11 eq238
    | (have j1 := eq11 (M.op (M.op (σ x) (σ y)) X0) (σ x)
       grind)
    | exact resolve eq238 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq756 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq770 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) ∨ (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq237 eq745
    | (have j0 := eq745 X0 X1
       grind)
    | exact resolve eq745 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq813 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) ∨ (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq237 eq770
    | (have j0 := eq770 X0 x
       grind)
    | exact resolve eq770 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq838 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq237 eq813
    | (have j0 := eq813 X0
       grind)
    | exact resolve eq813 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813
  have eq841 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) := by
    intro X0
    first
    | (have j0 := eq838 X0
       have j1 := eq187 (σ x) x (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq838 X0
       have r₂ := eq187 (σ x) (M.op (σ x) (σ y)) x (σ x)
       grind)
    | (have r₁ := eq838 X0
       have r₂ := eq187 (σ x) (σ y) x (k (M.op (σ x) (M.op (σ x) (σ y))) (σ x))
       grind)
    | exact resolve eq838 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq838
  have eq843 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq237 eq841
    | exact resolve eq841 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237 eq841
  have eq844 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have j1 := eq13 (M.op (σ x) (M.op (σ x) (σ y))) (σ x)
       grind)
    | (have r₁ := eq843
       have r₂ := eq13 (M.op (σ x) (M.op (σ x) (σ y))) (σ x)
       grind)
    | exact resolve eq843 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq1000 : (τ (M.op (σ x) (M.op (σ x) (σ y)))) = (k (τ (M.op (σ x) (M.op (σ x) (σ y)))) x) := by
    first
    | exact superpose eq844 eq141
    | exact resolve eq141 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq844
  have eq1233 : (M.op x y) = (k (M.op x y) (M.op x (M.op x y))) := by
    first
    | (have j0 := eq209 (M.op x (M.op x y))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq1234 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq188 eq1233
    | exact resolve eq1233 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1233
  have eq1247 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq1234 eq37
    | exact resolve eq37 eq1234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq1234
  have eq1248 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq20 eq1247
    | (have j0 := eq1247 X0
       grind)
    | exact resolve eq1247 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1247
  have eq2658 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) ≠ (M.op (M.op X0 X3) X4) ∨ (k X0 (M.op (M.op X0 X3) X4)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq13 X0 (M.op (M.op X0 X3) X4)
       have i₂ := eq176 X0 X3 X4 X1 X2
       grind)
    | exact superpose eq176 eq13
    | (have j0 := eq13 X0 (M.op (M.op X0 X3) X4)
       grind)
    | (have r₁ := eq13 (M.op X0 X4) (M.op X0 (M.op (M.op X0 X1) X2))
       have r₂ := eq176 X0 X1 X2 X4 (M.op X0 (M.op (M.op X0 X1) X2))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X0 X4) x)
       have r₂ := eq176 X0 X4 x X4 x
       grind)
    | exact resolve eq13 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2776 : ∀ X0 X3 X4 : G, (k X0 (M.op (M.op X0 X3) X4)) = X0 := by
    intro X0 X3 X4
    first
    | (have j0 := eq2658 X0 x x X3 X4
       grind)
    | (have r₁ := eq2658 X0 x x X4 x
       have r₂ := eq178 X0 x x X4 x
       grind)
    | (have r₁ := eq2658 X0 X4 x x x
       have r₂ := eq178 X0 x x X4 x
       grind)
    | exact resolve eq2658 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq2658
  have eq3378 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2776 X0 x x
       have i₂ := eq16 X0 X1 x x
       grind)
    | exact superpose eq16 eq2776
    | exact resolve eq2776 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3389 : ∀ X0 X1 : G, (σ y) = (k (σ y) (σ (M.op (M.op y X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq36 (M.op (M.op y X0) X1)
       have i₂ := eq2776 y X0 X1
       grind)
    | exact superpose eq2776 eq36
    | exact resolve eq36 eq2776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq2776
  have eq3398 : ∀ X0 X1 : G, (σ y) = (k (σ y) (σ (M.op (M.op y X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3389 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3389
    | (have j0 := eq3389 X0 X1
       grind)
    | exact resolve eq3389 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3389
  have eq3538 : ∀ X0 : G, (τ (σ y)) = (k y (τ (M.op (σ y) (M.op (σ y) X0)))) := by
    intro X0
    first
    | (have i₁ := eq107 (M.op sF3 (M.op sF3 x))
       have i₂ := eq3378 sF3 x
       grind)
    | exact superpose eq3378 eq107
    | exact resolve eq107 eq3378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq3378
  have eq3539 : ∀ X0 : G, y = (k y (τ (M.op (σ y) (M.op (σ y) X0)))) := by
    intro X0
    first
    | exact superpose eq31 eq3538
    | exact resolve eq3538 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3538
  have eq3587 : ∀ X0 X1 : G, (σ y) = (k (σ y) (σ (M.op y (M.op (M.op y X0) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3398 x x
       have i₂ := eq176 y X0 X1 x x
       grind)
    | exact superpose eq176 eq3398
    | exact resolve eq3398 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq3398
  have eq5123 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq687
       grind)
    | exact superpose eq687 eq39
    | exact resolve eq39 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq5124 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq5123
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5123
    | exact resolve eq5123 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5123
  have eq5126 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq5124
    | exact resolve eq5124 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5124
  have eq7641 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq5126 eq699
    | exact resolve eq699 eq5126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699 eq5126
  have eq7650 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq7641
       have r₂ := eq27
       grind)
    | exact resolve eq7641 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7641
  have eq7657 : y = (k y (τ (M.op (σ y) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq7650 eq3539
    | exact resolve eq3539 eq7650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3539
  have eq7686 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq7650 eq7657
    | exact resolve eq7657 eq7650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7657
  have eq7689 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq7686
    | exact resolve eq7686 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7686
  have eq7691 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq7689
       have r₂ := eq13 y x
       grind)
    | exact resolve eq7689 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7689
  have eq7693 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq687
       have i₂ := eq7691
       grind)
    | exact superpose eq7691 eq687
    | exact resolve eq687 eq7691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687 eq7691
  have eq7697 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7693
  have eq7737 : ∀ X0 : G, (M.op y x) = (M.op y (M.op y X0)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq184 y X0 x
       have i₂ := eq7697
       grind)
    | exact superpose eq7697 eq184
    | exact resolve eq184 eq7697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7751 : ∀ X0 : G, x = (M.op y (M.op y X0)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7697 eq7737
    | exact resolve eq7737 eq7697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7697 eq7737
  have eq7952 : ∀ X1 X2 X3 : G, x = (M.op (M.op (M.op y X1) X2) X3) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq185 y X1 X2 X3 x
       have i₂ := eq7751 x
       grind)
    | exact superpose eq7751 eq185
    | exact resolve eq185 eq7751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq7955 : ∀ X1 X2 : G, x = (M.op (M.op y X1) X2) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1 X2
    first
    | (have i₁ := eq16 y x X1 X2
       have i₂ := eq7751 x
       grind)
    | exact superpose eq7751 eq16
    | exact resolve eq16 eq7751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7751
  have eq7989 : ∀ X3 : G, x = (M.op x X3) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X3
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3⟩ := hcon
    have f7989_14 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op y X0) X1) X2) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0 X1 X2
      grind
    have f7989_15 : ∀ X0 X1 : G, x = (M.op (M.op y X0) X1) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      grind
    have f7989_24 : x ≠ (M.op x y) := by grind
    have f7989_25 : y ≠ (M.op x y) := by grind
    have f7989_26 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
    have f7989_27 : ∀ X0 X1 : G, x = (M.op (M.op y X0) X1) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      first
      | (have j0 := f7989_15 X0 X1
         grind)
      | (have r₁ := f7989_15 X0 X1
         have r₂ := f7989_24
         grind)
      | exact resolve f7989_15 f7989_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7989_28 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op y X0) X1) X2) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0 X1 X2
      first
      | (have j0 := f7989_14 X0 X1 X2
         grind)
      | (have r₁ := f7989_14 X0 X1 X2
         have r₂ := f7989_24
         grind)
      | exact resolve f7989_14 f7989_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7989_29 : ∀ X0 X1 : G, x = (M.op (M.op y X0) X1) ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      first
      | (have j0 := f7989_27 X0 X1
         grind)
      | (have r₁ := f7989_27 X0 X1
         have r₂ := f7989_25
         grind)
      | exact resolve f7989_27 f7989_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7989_30 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op y X0) X1) X2) ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0 X1 X2
      first
      | (have j0 := f7989_28 X0 X1 X2
         grind)
      | (have r₁ := f7989_28 X0 X1 X2
         have r₂ := f7989_25
         grind)
      | exact resolve f7989_28 f7989_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7989_31 : ∀ X0 X1 : G, x = (M.op (M.op y X0) X1) := by
      intro X0 X1
      first
      | (have j0 := f7989_29 X0 X1
         grind)
      | (have r₁ := f7989_29 X0 X1
         have r₂ := f7989_26
         grind)
      | exact resolve f7989_29 f7989_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7989_32 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op y X0) X1) X2) := by
      intro X0 X1 X2
      first
      | (have j0 := f7989_30 X0 X1 X2
         grind)
      | (have r₁ := f7989_30 X0 X1 X2
         have r₂ := f7989_26
         grind)
      | exact resolve f7989_30 f7989_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7989_33 : ∀ X2 : G, x = (M.op x X2) := by
      intro X2
      first
      | (have i₁ := f7989_32 x x X2
         have i₂ := f7989_31 x x
         grind)
      | exact superpose f7989_31 f7989_32
      | exact resolve f7989_32 f7989_31
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7989_36 : x ≠ x := by
      first
      | (have i₁ := f7989_24
         have i₂ := f7989_33 y
         grind)
      | exact superpose f7989_33 f7989_24
      | (have r₁ := f7989_24
         have r₂ := f7989_33 y
         grind)
      | exact resolve f7989_24 f7989_33
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7989_37 : False := by grind
    exact f7989_37
  clear eq7952 eq7955
  have eq8049 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq7989 y
       grind)
    | exact superpose eq7989 eq18
    | (have j1 := eq7989 y
       grind)
    | exact resolve eq18 eq7989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7989
  have eq8090 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq8049
  have eq8118 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq8090 eq240
    | exact resolve eq240 eq8090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8255 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8118 eq26
    | (have j1 := eq8118 (σ y) X0
       grind)
    | exact resolve eq26 eq8118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8306 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8090 eq8255
    | exact resolve eq8255 eq8090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8255
  have eq8403 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8306 eq1000
    | exact resolve eq1000 eq8306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8306
  have eq8451 : x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq8403
    | exact resolve eq8403 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8403
  have eq8499 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq756 x x
       have i₂ := eq8451
       grind)
    | exact superpose eq8451 eq756
    | (have j0 := eq756 x x
       grind)
    | (have r₁ := eq756 x x
       have r₂ := eq8451
       grind)
    | exact resolve eq756 eq8451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8451
  have eq8500 : x ≠ x ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq8499
  have eq8501 : x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq8500
  have eq8508 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op x X1) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq195 X0 x X1
       have i₂ := eq8501
       grind)
    | exact superpose eq8501 eq195
    | exact resolve eq195 eq8501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq8724 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8501
       have i₂ := eq8508 X0 x
       grind)
    | exact superpose eq8508 eq8501
    | exact resolve eq8501 eq8508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8501
  have eq8725 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq8508 X0 y
       grind)
    | (have i₁ := eq18
       have i₂ := eq8508 X0 x
       grind)
    | exact superpose eq8508 eq18
    | (have j1 := eq8508 X0 y
       grind)
    | exact resolve eq18 eq8508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8508
  have eq8766 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq8724 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8724
  have eq8787 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8725 eq8766
    | exact resolve eq8766 eq8725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8725 eq8766
  have eq8788 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq8787
  have eq8826 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq8788
       grind)
    | exact superpose eq8788 eq18
    | exact resolve eq18 eq8788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8827 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq8788
       grind)
    | exact superpose eq8788 eq24
    | exact resolve eq24 eq8788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq8836 : ∀ X0 X1 : G, (σ y) = (k (σ y) (σ (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X1)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq3587 X0 X1
       have i₂ := eq8788
       grind)
    | exact superpose eq8788 eq3587
    | exact resolve eq3587 eq8788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3587 eq8788
  have eq8853 : (σ y) = (k (σ y) (σ (M.op x (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq188 eq8836
    | exact resolve eq8836 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq8836
  have eq8859 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq8827
    | exact resolve eq8827 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8827
  have eq8861 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8826 eq8853
    | exact resolve eq8853 eq8826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8853
  have eq8865 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq8861
    | exact resolve eq8861 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8861
  have eq8869 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8859 eq8865
    | exact resolve eq8865 eq8859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8859 eq8865
  have eq8935 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8826 eq367
    | exact resolve eq367 eq8826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9458 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8869 eq756
    | (have j0 := eq756 (σ y) (σ y)
       grind)
    | (have r₁ := eq756 (σ y) (σ y)
       have r₂ := eq8869
       grind)
    | exact resolve eq756 eq8869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8869
  have eq9459 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9458
  have eq9460 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9459
  have eq9649 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9460 eq184
    | exact resolve eq184 eq9460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9664 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9460 eq9649
    | exact resolve eq9649 eq9460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9460 eq9649
  have eq9793 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) X0) X1) = (M.op (σ x) (M.op (σ y) (M.op (σ y) X2))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    intro X0 X1 X2
    first
    | exact superpose eq7650 eq177
    | exact resolve eq177 eq7650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq10147 : ∀ X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (M.op (σ y) X2))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    intro X2
    first
    | exact superpose eq441 eq9793
    | exact resolve eq9793 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9793
  have eq10160 : ∀ X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (M.op (σ y) X2))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    intro X2
    first
    | exact superpose eq8118 eq10147
    | (have j0 := eq10147 X2
       have j1 := eq8118 (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) X2))
       grind)
    | exact resolve eq10147 eq8118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8118 eq10147
  have eq10167 : ∀ X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (M.op (σ y) X2))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X2
    first
    | exact superpose eq8935 eq10160
    | (have j0 := eq10160 X2
       grind)
    | exact resolve eq10160 eq8935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10160
  have eq10168 : ∀ X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (M.op (σ y) X2))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X2
    first
    | (have j0 := eq10167 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10167
  have eq10170 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9664 eq10168
    | exact resolve eq10168 eq9664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10168
  have eq10171 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq10170
    | exact resolve eq10170 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10170
  have eq10214 : ∀ X1 X2 : G, (σ y) = (M.op (M.op (σ y) X1) X2) ∨ x = (M.op x y) := by
    intro X1 X2
    first
    | exact superpose eq9664 eq16
    | exact resolve eq16 eq9664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10264 : ∀ X0 : G, (σ y) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq7650 eq10214
    | exact resolve eq10214 eq7650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10266 : ∀ X1 : G, (σ y) = (M.op (σ y) X1) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq9664 eq10214
    | exact resolve eq10214 eq9664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9664 eq10214
  have eq10344 : ∀ X1 : G, (σ y) = (M.op (σ y) X1) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have j0 := eq10266 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10266
  have eq10346 : ∀ X0 : G, (σ y) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq10264 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10264
  have eq10357 : ∀ X0 : G, (σ y) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq8090 eq10346
    | (have j0 := eq10346 X0
       grind)
    | exact resolve eq10346 eq8090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10346
  have eq10360 : ∀ X0 : G, (σ y) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8935 eq10357
    | (have j0 := eq10357 X0
       grind)
    | exact resolve eq10357 eq8935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10357
  have eq10361 : ∀ X0 : G, (σ y) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq10360 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10360
  have eq10382 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10344 eq7650
    | exact resolve eq7650 eq10344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7650 eq10344
  have eq10420 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq10382
  have eq10428 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq8090 eq10420
    | exact resolve eq10420 eq8090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8090 eq10420
  have eq10434 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8935 eq10428
    | exact resolve eq10428 eq8935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8935 eq10428
  have eq10435 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq10434
  have eq10904 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10361 eq10171
    | (have j1 := eq10361 (σ y)
       grind)
    | exact resolve eq10171 eq10361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10171 eq10361
  have eq10942 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10904
  have eq10978 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10435 eq10942
    | exact resolve eq10942 eq10435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10435 eq10942
  have eq10979 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10978
  have eq11044 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq10979 eq240
    | exact resolve eq240 eq10979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq11969 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11044 eq26
    | (have j1 := eq11044 (σ y) X0
       grind)
    | exact resolve eq26 eq11044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11044
  have eq12055 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10979 eq11969
    | exact resolve eq11969 eq10979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10979 eq11969
  have eq12161 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12055 eq1000
    | exact resolve eq1000 eq12055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000 eq12055
  have eq12232 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq12161
    | exact resolve eq12161 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq12161
  have eq12284 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq756 x x
       have i₂ := eq12232
       grind)
    | exact superpose eq12232 eq756
    | (have j0 := eq756 x x
       grind)
    | (have r₁ := eq756 x x
       have r₂ := eq12232
       grind)
    | exact resolve eq756 eq12232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12232
  have eq12285 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq12284
  have eq12286 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq12285
  have eq12302 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq367 x X0
       have i₂ := eq12286
       grind)
    | exact superpose eq12286 eq367
    | exact resolve eq367 eq12286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq12347 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8826 eq12302
    | exact resolve eq12302 eq8826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8826 eq12302
  have eq12411 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12286
       have i₂ := eq12347 x
       grind)
    | exact superpose eq12347 eq12286
    | exact resolve eq12286 eq12347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12286 eq12347
  have eq12465 : x = (M.op x y) := by grind
  clear eq12411
  have eq12485 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq12465
       grind)
    | exact superpose eq12465 eq18
    | exact resolve eq18 eq12465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq12486 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq12465
       grind)
    | exact superpose eq12465 eq22
    | exact resolve eq22 eq12465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq12465
  have eq12528 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq12486 eq20
    | exact resolve eq20 eq12486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12486
  have eq12633 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq12485 eq1248
    | exact resolve eq1248 eq12485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248 eq12485
  have eq12672 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq12633
    | exact resolve eq12633 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq12633
  have eq12677 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq12528 eq12672
    | exact resolve eq12672 eq12528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12672
  have eq12852 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12677 eq756
    | (have j0 := eq756 (σ x) (σ x)
       grind)
    | (have r₁ := eq756 (σ x) (σ x)
       have r₂ := eq12677
       grind)
    | exact resolve eq756 eq12677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756 eq12677
  have eq12853 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq12852
  have eq12854 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq12853
  have eq12880 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq12854 eq441
    | exact resolve eq441 eq12854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12900 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq12854 eq184
    | exact resolve eq184 eq12854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq12916 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq12854 eq12900
    | exact resolve eq12900 eq12854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12854 eq12900
  have eq12921 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq12880 eq12916
    | (have j0 := eq12916 (σ y)
       grind)
    | exact resolve eq12916 eq12880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12880 eq12916
  have eq12952 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq12921 eq441
    | exact resolve eq441 eq12921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441 eq12921
  have eq13071 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12952 eq26
    | (have j1 := eq12952 (σ y)
       grind)
    | exact resolve eq26 eq12952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq12952
  have eq13165 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq13071 eq27
    | exact resolve eq27 eq13071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq13071
  have eq13202 : False := by grind
  exact eq13202

/-- `Equation4419`: `x ◇ (x ◇ y) = (z ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyx_pyx_pxy_Equation4419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X1) X0) := by
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
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
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
  have eq45 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X2) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X2 X1) X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X1)) = (M.op (M.op X2 X1) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 X1) X0 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X0)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X0 (M.op x X1)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq28 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq79 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq45
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq46
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq104
    | exact resolve eq104 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq110
    | exact resolve eq110 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq204 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 y))) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 y) X0
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq28 eq58
    | (have j0 := eq58 (σ x)
       grind)
    | exact resolve eq58 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) X1) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq363 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 y)) = (M.op (M.op X0 y) (M.op (M.op x y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq58 (M.op X0 y)
       have i₂ := eq204 X0 sF3
       grind)
    | (have i₁ := eq58 (M.op x y)
       have i₂ := eq204 X0 sF3
       grind)
    | exact superpose eq204 eq58
    | exact resolve eq58 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq364 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 y)) = (M.op (M.op x y) (M.op (M.op x y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq363 X0
       have i₂ := eq204 X0 (M.op sF0 sF3)
       grind)
    | (have i₁ := eq363 x
       have i₂ := eq204 X0 (M.op sF0 sF3)
       grind)
    | exact superpose eq204 eq363
    | exact resolve eq363 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq374 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 y)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq58 eq364
    | exact resolve eq364 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq385 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op X2 (M.op X0 y)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X0 (M.op X0 y) X1 X2
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq54
    | exact resolve eq54 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X1) = (M.op (M.op X2 (M.op X0 (σ y))) X1) := by
    intro X0 X1 X2
    first
    | exact superpose eq58 eq54
    | exact resolve eq54 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) y)) := by
    intro X0
    first
    | exact superpose eq211 eq57
    | exact resolve eq57 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq211 eq58
    | exact resolve eq58 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq211 eq478
    | exact resolve eq478 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq480 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) y)) := by
    intro X0
    first
    | exact superpose eq211 eq477
    | exact resolve eq477 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq489 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq58 eq479
    | exact resolve eq479 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq490 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq480 X0
       have i₂ := eq57 sF4
       grind)
    | exact superpose eq57 eq480
    | exact resolve eq480 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq535 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X1 X2 X3
       have i₂ := eq54 X1 (M.op X1 X2) X3 X0
       grind)
    | (have i₁ := eq56 X1 X2 X3
       have i₂ := eq54 X0 (M.op X1 X2) X3 X1
       grind)
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq626 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 y) X0)) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 y X0 X0
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq52
    | exact resolve eq52 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq627 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq58 eq52
    | exact resolve eq52 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq711 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq211 eq627
    | (have j0 := eq627 X0 (σ x)
       grind)
    | exact resolve eq627 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq712 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq626 X0 x
       have i₂ := eq204 x X0
       grind)
    | (have i₁ := eq626 x x
       have i₂ := eq204 X0 x
       grind)
    | exact superpose eq204 eq626
    | (have j0 := eq626 X0 x
       grind)
    | exact resolve eq626 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq757 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq374 sF4
       have i₂ := eq57 sF4
       grind)
    | exact superpose eq57 eq374
    | exact resolve eq374 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1067 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) y) (M.op X1 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (M.op X0 X1)
       have i₂ := eq53 X1 y (M.op X0 X1) X0
       grind)
    | exact superpose eq53 eq57
    | exact resolve eq57 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1068 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) (σ y)) (M.op X1 (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq58 (M.op x X0)
       have i₂ := eq53 X0 sF3 (M.op x X0) x
       grind)
    | exact superpose eq53 eq58
    | exact resolve eq58 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1115 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq211 eq1068
    | exact resolve eq1068 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq1116 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x y) (M.op X1 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1067 X0 X1
       have i₂ := eq204 (M.op X0 X1) (M.op X1 (M.op X1 y))
       grind)
    | exact superpose eq204 eq1067
    | exact resolve eq1067 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067
  have eq1139 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq58 eq1115
    | exact resolve eq1115 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq1115
  have eq1140 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x y) (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1116 X0 X1
       have i₂ := eq57 X1
       grind)
    | exact superpose eq57 eq1116
    | exact resolve eq1116 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq1174 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq77 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1899 : (M.op (M.op x y) y) = (M.op y (M.op (M.op (σ x) (σ y)) y)) := by
    first
    | (have i₁ := eq711 y
       have i₂ := eq204 sF4 y
       grind)
    | exact superpose eq204 eq711
    | exact resolve eq711 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq1957 : (M.op (M.op x y) y) = (M.op y (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq712 y
       have i₂ := eq204 sF0 y
       grind)
    | exact superpose eq204 eq712
    | exact resolve eq712 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1958 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op x y) (σ y))) := by
    first
    | exact superpose eq211 eq712
    | exact resolve eq712 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq2006 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 y) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op x y) y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1899 eq52
    | exact resolve eq52 eq1899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1899
  have eq2025 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq2006 X0
       have i₂ := eq14 sF4 y sF0
       grind)
    | exact superpose eq14 eq2006
    | exact resolve eq2006 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2006
  have eq2027 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) y))) := by
    first
    | (have i₁ := eq2025 x
       have i₂ := eq14 sF4 y x
       grind)
    | exact superpose eq14 eq2025
    | exact resolve eq2025 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2025
  have eq2028 : (M.op (M.op x y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq2027
       have i₂ := eq57 sF4
       grind)
    | exact superpose eq57 eq2027
    | exact resolve eq2027 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2027
  have eq2056 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op X0 y) (M.op x y))) = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1957 eq52
    | exact resolve eq52 eq1957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957
  have eq2075 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) y)) = (M.op (M.op x y) (M.op (M.op X0 y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq2056 X0
       have i₂ := eq14 sF0 y sF0
       grind)
    | exact superpose eq14 eq2056
    | exact resolve eq2056 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2056
  have eq2079 : (M.op (M.op x y) (M.op (M.op x y) y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) y))) := by
    first
    | (have i₁ := eq2075 x
       have i₂ := eq14 sF0 y x
       grind)
    | exact superpose eq14 eq2075
    | exact resolve eq2075 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2075
  have eq2080 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq2079
       have i₂ := eq57 sF0
       grind)
    | exact superpose eq57 eq2079
    | exact resolve eq2079 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2079
  have eq2082 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op X0 (σ y)) (M.op x y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1958 eq52
    | exact resolve eq52 eq1958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1958
  have eq2101 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) (σ y))) = (M.op (M.op x y) (M.op (M.op X0 (σ y)) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq2082 X0
       have i₂ := eq14 sF0 sF3 sF4
       grind)
    | exact superpose eq14 eq2082
    | exact resolve eq2082 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2082
  have eq2105 : (M.op (M.op x y) (M.op (M.op x y) (σ y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (σ y)))) := by
    first
    | (have i₁ := eq2101 x
       have i₂ := eq14 sF0 sF3 x
       grind)
    | exact superpose eq14 eq2101
    | exact resolve eq2101 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2101
  have eq2106 : (M.op (M.op x y) (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq490 eq2105
    | exact resolve eq2105 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490 eq2105
  have eq2129 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq1139 X0 (M.op X0 y)
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq1139
    | exact resolve eq1139 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2217 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq374 eq2129
    | exact resolve eq2129 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374 eq2129
  have eq2228 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq757 eq2217
    | exact resolve eq2217 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2217
  have eq2229 : ∀ X0 : G, (M.op (M.op x y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq2028 eq2228
    | exact resolve eq2228 eq2028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2228
  have eq2237 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq489 eq2229
    | exact resolve eq2229 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489 eq2229
  have eq2441 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) (M.op x y)) = (M.op (M.op x y) (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq2106 eq52
    | exact resolve eq52 eq2106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2454 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | exact superpose eq1140 eq2441
    | exact resolve eq2441 eq1140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2441
  have eq2458 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq2454
       have i₂ := eq14 sF0 sF4 sF0
       grind)
    | exact superpose eq14 eq2454
    | exact resolve eq2454 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2454
  have eq2460 : (M.op (M.op x y) (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq2106 eq2458
    | exact resolve eq2458 eq2106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2106 eq2458
  have eq2462 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2080 eq2460
    | exact resolve eq2460 eq2080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2460
  have eq2553 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op X0 y))) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1140 eq206
    | exact resolve eq206 eq1140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2557 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 y))) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1139 eq206
    | exact resolve eq206 eq1139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2643 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq2557 X0
       have i₂ := eq14 sF4 sF4 sF0
       grind)
    | exact superpose eq14 eq2557
    | exact resolve eq2557 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2557
  have eq2647 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op X0 y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq2553 X0
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq2553
    | exact resolve eq2553 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2553
  have eq2697 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq2237 eq2643
    | exact resolve eq2643 eq2237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2237 eq2643
  have eq2701 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op X0 y))) := by
    intro X0
    first
    | exact superpose eq2080 eq2647
    | exact resolve eq2647 eq2080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2080 eq2647
  have eq2733 : ∀ X0 : G, (M.op (M.op x y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 y))) := by
    intro X0
    first
    | exact superpose eq2028 eq2697
    | exact resolve eq2697 eq2028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2028 eq2697
  have eq2737 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2701 X0
       have i₂ := eq206 X0 sF0
       grind)
    | exact superpose eq206 eq2701
    | exact resolve eq2701 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2701
  have eq2751 : ∀ X0 : G, (M.op (M.op x y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq2733 X0
       have i₂ := eq206 X0 sF4
       grind)
    | exact superpose eq206 eq2733
    | exact resolve eq2733 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq2733
  have eq2754 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq2737 x
       have i₂ := eq14 sF0 x sF0
       grind)
    | exact superpose eq14 eq2737
    | exact resolve eq2737 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2737
  have eq2763 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq2751 x
       have i₂ := eq14 sF4 x sF0
       grind)
    | exact superpose eq14 eq2751
    | exact resolve eq2751 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2751
  have eq2769 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq2462 eq2763
    | exact resolve eq2763 eq2462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2763
  have eq2789 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq1140 eq2754
    | exact resolve eq2754 eq1140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2754
  have eq2845 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq1139 eq2769
    | exact resolve eq2769 eq1139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1139 eq2769
  have eq3845 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op x y) (M.op X2 X1)) X3) = (M.op (M.op (M.op X0 (M.op y X1)) y) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq385 (M.op X2 X1) X3 y
       have i₂ := eq52 X2 X1 y X0
       grind)
    | exact superpose eq52 eq385
    | exact resolve eq385 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4027 : ∀ X1 X2 X3 : G, (M.op (M.op x y) X3) = (M.op (M.op (M.op x y) (M.op X2 X1)) X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq3845 x X1 X2 X3
       have i₂ := eq204 (M.op x (M.op y X1)) X3
       grind)
    | exact superpose eq204 eq3845
    | exact resolve eq3845 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3845
  have eq4087 : ∀ X3 : G, (M.op (M.op x y) X3) = (M.op (M.op (M.op x y) (M.op x y)) X3) := by
    intro X3
    first
    | exact superpose eq2789 eq4027
    | (have j0 := eq4027 y x X3
       grind)
    | exact resolve eq4027 eq2789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4027
  have eq4151 : (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) = (k (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op x y))) := by grind
  have eq4226 : (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) = (k (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq2789 eq4151
    | exact resolve eq4151 eq2789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4151
  have eq4260 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (k (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq4087 eq4226
    | exact resolve eq4226 eq4087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4226
  have eq4276 : (M.op (M.op x y) (M.op x y)) = (k (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq2789 eq4260
    | exact resolve eq4260 eq2789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2789 eq4260
  have eq4441 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) = (M.op (M.op X2 (M.op (M.op x y) (σ y))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq386 (M.op X0 y) X1 X2
       have i₂ := eq204 X0 sF3
       grind)
    | (have i₁ := eq386 (M.op x y) X1 X2
       have i₂ := eq204 X0 sF3
       grind)
    | exact superpose eq204 eq386
    | exact resolve eq386 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4457 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X2 X1)) X3) = (M.op (M.op (M.op X0 (M.op (σ y) X1)) (σ y)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq386 (M.op X0 X1) X1 sF3
       have i₂ := eq52 X0 X1 sF3 X3
       grind)
    | exact superpose eq52 eq386
    | exact resolve eq386 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq4652 : ∀ X1 X2 X3 : G, (M.op (M.op (σ x) (σ y)) X3) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X2 X1)) X3) := by
    intro X1 X2 X3
    first
    | exact superpose eq211 eq4457
    | exact resolve eq4457 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq4457
  have eq4666 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq386 eq4441
    | exact resolve eq4441 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386 eq4441
  have eq4720 : ∀ X3 : G, (M.op (M.op (σ x) (σ y)) X3) = (M.op (M.op (M.op x y) (M.op x y)) X3) := by
    intro X3
    first
    | exact superpose eq2845 eq4652
    | exact resolve eq4652 eq2845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2845 eq4652
  have eq4732 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq757 eq4666
    | exact resolve eq4666 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757 eq4666
  have eq4773 : ∀ X3 : G, (M.op (M.op x y) X3) = (M.op (M.op (σ x) (σ y)) X3) := by
    intro X3
    first
    | exact superpose eq4087 eq4720
    | exact resolve eq4720 eq4087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4720
  have eq4781 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) = (M.op (M.op (M.op x y) (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq2462 eq4732
    | exact resolve eq4732 eq2462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4732
  have eq4807 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq4087 eq4781
    | exact resolve eq4781 eq4087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4087 eq4781
  have eq4818 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4807 X0 X1
       have i₂ := eq385 X0 X1 sF4
       grind)
    | exact superpose eq385 eq4807
    | exact resolve eq4807 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385 eq4807
  have eq4834 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq210 eq4773
    | exact resolve eq4773 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq4773
  have eq6066 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4818 X1 X2
       have i₂ := eq54 sF0 X1 X2 x
       grind)
    | (have i₁ := eq4818 X1 X2
       have i₂ := eq54 X0 X1 X2 sF0
       grind)
    | exact superpose eq54 eq4818
    | exact resolve eq4818 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq6659 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq1140 eq535
    | exact resolve eq535 eq1140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535 eq1140
  have eq6975 : ∀ X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op (M.op x y) X2) := by
    intro X1 X2
    first
    | exact superpose eq4818 eq6659
    | exact resolve eq6659 eq4818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4818 eq6659
  have eq19080 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq111 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19081 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq19080
    | exact resolve eq19080 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19080
  have eq19092 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq19081
       have r₂ := eq29
       grind)
    | exact resolve eq19081 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19081
  have eq19104 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  have eq19121 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq19092 eq6066
    | exact resolve eq6066 eq19092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19122 : (M.op (σ y) (σ x)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq19092 eq6975
    | exact resolve eq6975 eq19092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19092
  have eq19175 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq19104 eq111
    | exact resolve eq111 eq19104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq19104
  have eq19184 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq19175
  have eq19280 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq19121
    | (have j0 := eq19121 (σ y)
       grind)
    | exact resolve eq19121 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19121
  have eq19579 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq19122 eq19184
    | exact resolve eq19184 eq19122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19122 eq19184
  have eq19602 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq19579
  have eq19626 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq19602 eq19280
    | exact resolve eq19280 eq19602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19280 eq19602
  have eq19666 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq19626
  have eq19695 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq19666
       have r₂ := eq29
       grind)
    | exact resolve eq19666 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19666
  have eq19714 : (M.op y x) = (M.op (M.op x y) y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq57 y
       have i₂ := eq19695
       grind)
    | exact superpose eq19695 eq57
    | exact resolve eq57 eq19695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq19715 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq204 y X0
       have i₂ := eq19695
       grind)
    | exact superpose eq19695 eq204
    | exact resolve eq204 eq19695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq19723 : (k x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq19695
  have eq19952 : (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq19715 eq19714
    | exact resolve eq19714 eq19715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19714 eq19715
  have eq20043 : (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq19952
  have eq20082 : (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq20043
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq20043
    | exact resolve eq20043 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20043
  have eq20213 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq19723
       grind)
    | exact superpose eq19723 eq46
    | exact resolve eq46 eq19723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq19723
  have eq20712 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq20213
       have i₂ := eq20082
       grind)
    | exact superpose eq20082 eq20213
    | exact resolve eq20213 eq20082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20082 eq20213
  have eq20755 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq20712
  have eq20759 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq22 eq20755
    | exact resolve eq20755 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20755
  have eq20772 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20759 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq20759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20773 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq20772
  have eq20777 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq28 eq20773
    | exact resolve eq20773 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20773
  have eq20788 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq20777
       have r₂ := eq29
       grind)
    | exact resolve eq20777 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20777
  have eq20825 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  have eq20842 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq20788 eq6066
    | exact resolve eq6066 eq20788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6066
  have eq20843 : (M.op (σ y) (σ x)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20788 eq6975
    | exact resolve eq6975 eq20788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6975 eq20788
  have eq20901 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20825 eq20759
    | exact resolve eq20759 eq20825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20759 eq20825
  have eq20904 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq20901
  have eq21015 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28 eq20842
    | (have j0 := eq20842 (σ y)
       grind)
    | exact resolve eq20842 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20842
  have eq21380 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20843 eq20904
    | exact resolve eq20904 eq20843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20843 eq20904
  have eq21405 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq21380
  have eq21432 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21405 eq21015
    | exact resolve eq21015 eq21405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21015 eq21405
  have eq21476 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq21432
  have eq21507 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq21476
       have r₂ := eq29
       grind)
    | exact resolve eq21476 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21476
  have eq21525 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq21507 eq31
    | exact resolve eq31 eq21507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq21507
  have eq21660 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq21525
    | exact resolve eq21525 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq21525
  have eq21661 : x = y := by grind
  clear eq21660
  have eq21668 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq21661
       grind)
    | exact superpose eq21661 eq20
    | exact resolve eq20 eq21661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq21669 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq21661
       grind)
    | exact superpose eq21661 eq26
    | exact resolve eq26 eq21661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq21661
  have eq21791 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq21669
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21669
    | exact resolve eq21669 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21669
  have eq21792 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21791 eq28
    | exact resolve eq28 eq21791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq21791
  have eq21933 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq21668
       grind)
    | exact superpose eq21668 eq79
    | exact resolve eq79 eq21668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq21934 : (M.op x (M.op x y)) = (k (M.op x y) x) := by grind
  have eq21963 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22 eq21933
    | exact resolve eq21933 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21933
  have eq22053 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  have eq22054 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21792 eq22053
    | exact resolve eq22053 eq21792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22053
  have eq22067 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22054
       have r₂ := eq29
       grind)
    | exact resolve eq22054 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22054
  have eq22072 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21792 eq22067
    | exact resolve eq22067 eq21792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22067
  have eq22077 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22072 eq29
    | exact resolve eq29 eq22072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22090 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22072 eq2462
    | exact resolve eq2462 eq22072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2462
  have eq22097 : (M.op (σ x) (σ x)) = (M.op (M.op x y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22072 eq4834
    | exact resolve eq4834 eq22072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4834
  have eq22105 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21792 eq22097
    | exact resolve eq22097 eq21792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22097
  have eq23680 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22090 eq22105
    | exact resolve eq22105 eq22090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22090 eq22105
  have eq23711 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq23680
  have eq23733 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23711 eq4276
    | exact resolve eq4276 eq23711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4276 eq23711
  have eq23816 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22072 eq23733
    | exact resolve eq23733 eq22072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22072 eq23733
  have eq23829 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq23816
  have eq23849 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23829 eq21963
    | exact resolve eq21963 eq23829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21963 eq23829
  have eq23860 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq23849
  have eq23866 : x = (M.op x y) := by
    first
    | (have r₁ := eq23860
       have r₂ := eq22077
       grind)
    | exact resolve eq23860 eq22077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22077 eq23860
  have eq23888 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq23866 eq22
    | exact resolve eq22 eq23866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq23981 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq23866 eq21934
    | exact resolve eq21934 eq23866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21934
  have eq23984 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq23981
       have i₂ := eq21668
       grind)
    | exact superpose eq21668 eq23981
    | exact resolve eq23981 eq21668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21668 eq23981
  have eq24065 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq23888
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23888
    | exact resolve eq23888 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23888
  have eq24067 : x = (k x x) := by
    first
    | exact superpose eq23866 eq23984
    | exact resolve eq23984 eq23866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23866 eq23984
  have eq24362 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1174 x
       have i₂ := eq24067
       grind)
    | exact superpose eq24067 eq1174
    | (have j0 := eq1174 x
       grind)
    | exact resolve eq1174 eq24067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174 eq24067
  have eq24369 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq24362
  have eq24378 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq24369
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24369
    | exact resolve eq24369 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq24369
  have eq24391 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21792 eq24378
    | exact resolve eq24378 eq21792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21792 eq24378
  have eq24402 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24065 eq24391
    | exact resolve eq24391 eq24065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24065 eq24391
  have eq24412 : False := by grind
  exact eq24412

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxy_pyy_pxy_pyy_pxy_Equation442 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law442 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq41 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq37 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq37 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq40 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq40 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq40 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 X0 X1
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq44
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       have j1 := eq41 X1 X0
       grind)
    | (have r₁ := eq49 X1 X0
       have r₂ := eq41 X0 X1
       grind)
    | (have r₁ := eq49 X0 X0
       have r₂ := eq41 X0 X0
       grind)
    | exact resolve eq49 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq49
  have eq152 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq159 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq152 X0 X1
       have j1 := eq51 X0 X1
       grind)
    | (have r₁ := eq152 X0 X1
       have r₂ := eq51 X0 X1
       grind)
    | (have r₁ := eq152 X0 X0
       have r₂ := eq51 X0 X0
       grind)
    | exact resolve eq152 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq152
  have eq305 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq159 (σ X0) (σ X1)
       grind)
    | exact superpose eq159 eq15
    | exact resolve eq15 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq312 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq305 X0 X1
       have i₂ := eq159 X0 X1
       grind)
    | exact superpose eq159 eq305
    | exact resolve eq305 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq305
  have eq314 : False := by grind
  exact eq314

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pxy_pxx_pxy_Equation442 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law442 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq15
    | exact resolve eq15 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq34
    | exact resolve eq34 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq34
  have eq52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq37 X1
       grind)
    | exact superpose eq37 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq77 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq55 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq55
    | exact resolve eq55 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq248 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq223 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq223
    | (have j0 := eq223 X0 X1
       grind)
    | exact resolve eq223 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq253 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq248 X0 X1
       have j1 := eq77 X1 X0
       grind)
    | (have r₁ := eq248 X1 X0
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq248 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq248 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq248
  have eq257 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq253 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq253
    | exact resolve eq253 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq253 (σ X0) X1
       grind)
    | exact superpose eq253 eq15
    | (have j1 := eq253 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq271 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq257 X1 (τ X0)
       grind)
    | exact superpose eq257 eq18
    | (have j1 := eq257 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq257
  have eq524 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq271 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq271
    | exact resolve eq271 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq562 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq524 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq524
    | (have j0 := eq524 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq524 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq1113 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq262 x y
       grind)
    | exact superpose eq262 eq16
    | (have j1 := eq262 x y
       grind)
    | exact resolve eq16 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq1140 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1113
       have i₂ := eq562 x y
       grind)
    | exact superpose eq562 eq1113
    | (have j1 := eq562 (σ x) (σ y)
       grind)
    | (have r₁ := eq1113
       have r₂ := eq562 x y
       grind)
    | (have r₁ := eq1113
       have r₂ := eq562 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1113
       have r₂ := eq562 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1113 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562 eq1113
  have eq1141 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1140
  have eq1207 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1141
       grind)
    | exact superpose eq1141 eq10
    | exact resolve eq10 eq1141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq1251 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1207
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1207
    | exact resolve eq1207 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207
  have eq1252 : x = y := by grind
  clear eq1251
  have eq1254 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1252
       grind)
    | exact superpose eq1252 eq16
    | exact resolve eq16 eq1252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252
  have eq1255 : False := by grind
  exact eq1255

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxy_pxx_pxy_Equation442 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law442 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq65 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 X0
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq78 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq77 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq83 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq78 (σ X0)
       grind)
    | exact superpose eq78 eq15
    | exact resolve eq15 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq83
    | exact resolve eq83 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq83
  have eq107 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq65 (σ X0) (σ X0)
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq65
    | exact resolve eq65 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq207 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq210 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq205 X0 X1
       have i₂ := eq90 X1
       grind)
    | exact superpose eq90 eq205
    | (have j0 := eq205 X0 X1
       grind)
    | exact resolve eq205 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq1333 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq207 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq207
    | exact resolve eq207 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq1392 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1333 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1333
    | (have j0 := eq1333 X0 X1
       grind)
    | exact resolve eq1333 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1333
  have eq3226 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq210 x y
       grind)
    | exact superpose eq210 eq16
    | (have j1 := eq210 x y
       grind)
    | exact resolve eq16 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq5735 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3226
       have i₂ := eq1392 x y
       grind)
    | exact superpose eq1392 eq3226
    | (have j1 := eq1392 x y
       grind)
    | (have r₁ := eq3226
       have r₂ := eq1392 x y
       grind)
    | (have r₁ := eq3226
       have r₂ := eq1392 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq3226
       have r₂ := eq1392 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3226 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392
  have eq5736 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq5735
  have eq5738 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5736
       grind)
    | exact superpose eq5736 eq16
    | exact resolve eq16 eq5736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5736
  have eq5739 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5738
       have r₂ := eq90 x
       grind)
    | exact resolve eq5738 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5738
  have eq5741 : (M.op x y) = (k x y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by grind
  clear eq5739
  have eq5790 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3226
       have i₂ := eq5741
       grind)
    | exact superpose eq5741 eq3226
    | exact resolve eq3226 eq5741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3226 eq5741
  have eq5791 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by grind
  clear eq5790
  have eq5792 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq5791
  have eq5796 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5792
       grind)
    | exact superpose eq5792 eq10
    | exact resolve eq10 eq5792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5792
  have eq5852 : x = y ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq5796
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5796
    | exact resolve eq5796 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5796
  have eq5855 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5852
       grind)
    | exact superpose eq5852 eq16
    | exact resolve eq16 eq5852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5852
  have eq5856 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq5855
       have r₂ := eq90 x
       grind)
    | exact resolve eq5855 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq5855
  have eq5860 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq107 y
       have i₂ := eq5856
       grind)
    | exact superpose eq5856 eq107
    | exact resolve eq107 eq5856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq5870 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq5856
       grind)
    | exact superpose eq5856 eq10
    | exact resolve eq10 eq5856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5856
  have eq5926 : x = (M.op y y) := by
    first
    | (have i₁ := eq5870
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5870
    | exact resolve eq5870 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5870
  have eq5961 : x = (M.op x y) := by
    first
    | (have i₁ := eq65 y y
       have i₂ := eq5926
       grind)
    | exact superpose eq5926 eq65
    | exact resolve eq65 eq5926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq5926
  have eq5990 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5860
       grind)
    | exact superpose eq5860 eq16
    | exact resolve eq16 eq5860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5860
  have eq6009 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq5990
       have i₂ := eq5961
       grind)
    | exact superpose eq5961 eq5990
    | exact resolve eq5990 eq5961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5961 eq5990
  have eq6010 : False := by grind
  exact eq6010

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pxy_pyx_Equation442 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law442 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq48 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq48 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq48 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq51 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq49 (σ X0)
       grind)
    | exact superpose eq49 eq15
    | exact resolve eq15 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq51 X0
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq51
    | exact resolve eq51 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq51
  have eq81 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 X1
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq81
    | (have j0 := eq81 X0 X1
       grind)
    | exact resolve eq81 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq96 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq255 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq87 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq87 X0 X1
       grind)
    | exact superpose eq87 eq13
    | (have j0 := eq13 X0 (σ X0)
       have j1 := eq87 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq87 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq87 X0 X1
       grind)
    | exact resolve eq13 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq271 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq255 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq278 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq271 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq271 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq271 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq288 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq278 X0 X1
       have j1 := eq96 X0 (σ X1)
       grind)
    | (have r₁ := eq278 X0 X1
       have r₂ := eq96 X0 X1
       grind)
    | exact resolve eq278 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq278
  have eq296 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq288 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq288
    | (have j0 := eq288 X0 X1
       grind)
    | exact resolve eq288 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq297 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq296 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq301 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq297 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq297
    | exact resolve eq297 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq313 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq297 x y
       grind)
    | exact superpose eq297 eq16
    | exact resolve eq16 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq380 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq301 X0 (τ X1)
       grind)
    | exact superpose eq301 eq17
    | exact resolve eq17 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq301
  have eq396 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq380 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq380
    | exact resolve eq380 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq404 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq396 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq396
    | exact resolve eq396 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq416 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq313
       have i₂ := eq404 x y
       grind)
    | exact superpose eq404 eq313
    | exact resolve eq313 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313 eq404
  have eq417 : False := by grind
  exact eq417

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_y_pyx_Equation442 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law442 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X0)))) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op X0 (M.op x y)))) := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 (M.op X2 X0))) = (M.op (M.op X1 (M.op X1 (M.op X2 X0))) (M.op X3 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 (M.op X1 (M.op X2 X0))) X3 X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X0) X0 X0
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq71 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq73 : y ≠ (M.op x y) ∨ x = (M.op x x) ∨ x = (k y x) := by
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
  have eq74 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ (k y (k y x))) = (k (σ y) (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq36 (k y x)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq36
    | exact resolve eq36 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq16
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq91 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
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
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq91
    | (have j0 := eq91 (σ X0) (σ X1)
       grind)
    | exact resolve eq91 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq91
    | (have j0 := eq91 (σ y) (σ X0)
       grind)
    | exact resolve eq91 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq91 y x
       grind)
    | exact superpose eq91 eq70
    | (have j1 := eq91 y x
       grind)
    | exact resolve eq70 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq114
    | exact resolve eq114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq117 eq91
    | (have j0 := eq91 (σ y) (σ x)
       grind)
    | exact resolve eq91 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq120
    | exact resolve eq120 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq124 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq121
       have r₂ := eq27
       grind)
    | exact resolve eq121 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq126 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq124
    | exact resolve eq124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq136 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq147 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq136 eq16
    | exact resolve eq16 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X0 (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq126 eq51
    | exact resolve eq51 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq230 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq223 eq14
    | exact resolve eq14 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 (M.op X1 X2)) X1
       have i₂ := eq54 (M.op X1 X2) X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq230 eq223
    | exact resolve eq223 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq248 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq230 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq230
       grind)
    | exact resolve eq13 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq248 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq252 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq247
  have eq282 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq293 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq251 eq85
    | exact resolve eq85 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq329 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq360 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq126 eq74
    | (have r₁ := eq74
       have r₂ := eq126
       grind)
    | exact resolve eq74 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq126
  have eq361 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq360
  have eq362 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq230 eq293
    | exact resolve eq293 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230 eq293
  have eq366 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) := by grind
  clear eq362
  have eq368 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq366
    | exact resolve eq366 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq371 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq91 y y
       have i₂ := eq368
       grind)
    | exact superpose eq368 eq91
    | (have j0 := eq91 y y
       grind)
    | exact resolve eq91 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq372 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq371
  have eq375 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq372
       grind)
    | exact superpose eq372 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq372
       grind)
    | exact resolve eq13 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq377 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op X0 y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 y
       have i₂ := eq372
       grind)
    | exact superpose eq372 eq14
    | exact resolve eq14 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq375 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq462 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq95 X0 X0
       grind)
    | exact superpose eq95 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq95 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq95 X0 X0
       grind)
    | exact resolve eq13 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (σ X0) (σ X1)
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq54
    | (have j1 := eq95 X0 X1
       grind)
    | exact resolve eq54 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq467 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq95 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq469 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq462 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq462 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq462 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq547 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X1 (M.op X1 X0)) (M.op X4 (M.op X4 (M.op X2 (M.op X2 (M.op X3 X0)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X1 (M.op X1 (M.op X2 X0))) X1 X0 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq553 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 y)) = (M.op (M.op X0 (M.op X0 y)) (M.op X2 (M.op X2 (M.op X1 (M.op X1 (M.op x y)))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq52
  have eq702 : y = (M.op y (M.op y y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq377 y
       have i₂ := eq372
       grind)
    | exact superpose eq372 eq377
    | exact resolve eq377 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq377
  have eq720 : y = (M.op y (M.op y y)) ∨ y = (M.op x y) := by grind
  clear eq702
  have eq909 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq361 eq117
    | exact resolve eq117 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq912 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq909
  have eq920 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq912 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq912
       grind)
    | exact resolve eq13 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq926 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq920 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq943 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq926 eq117
    | exact resolve eq117 eq926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq926
  have eq946 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq943
  have eq951 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq946
    | exact resolve eq946 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq953 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq951
       have r₂ := eq27
       grind)
    | exact resolve eq951 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq955 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq953 eq26
    | exact resolve eq26 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953
  have eq1104 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq282 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq282
    | (have j0 := eq282 X0 y
       grind)
    | exact resolve eq282 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq1171 : ∀ X0 : G, (k X0 (τ (σ y))) = (τ (M.op (σ y) (σ X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq251 eq329
    | exact resolve eq329 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq329
  have eq1181 : ∀ X0 : G, (k X0 y) = (τ (M.op (σ y) (σ X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq1171
    | exact resolve eq1171 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1171
  have eq2324 : (σ (k y (k y x))) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (k (σ y) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq97 (k y x)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq97
    | exact resolve eq97 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2343 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ (k y X0)) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq97 eq54
    | (have j1 := eq97 X0
       grind)
    | exact resolve eq54 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq2345 : ∀ X0 : G, (σ y) ≠ (σ (k y X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq97 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq3385 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq467 x y
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq467
    | (have j0 := eq467 x y
       grind)
    | exact resolve eq467 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq3409 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3385
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3385
    | exact resolve eq3385 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3385
  have eq3466 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq3409
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3409
    | exact resolve eq3409 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3409
  have eq3514 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq3466
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3466
    | exact resolve eq3466 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3466
  have eq3550 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3514
    | exact resolve eq3514 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3514
  have eq5286 : (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq464 y x
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq464
    | (have j0 := eq464 y x
       grind)
    | exact resolve eq464 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq5291 : (k (σ (M.op x y)) (σ x)) = (M.op (k (σ (M.op x y)) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq136 eq464
    | (have j0 := eq464 (M.op x y) x
       grind)
    | exact resolve eq464 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq5352 : (k (σ (M.op x y)) (σ x)) = (M.op (k (σ (M.op x y)) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq5291
    | exact resolve eq5291 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5291
  have eq5357 : (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5286
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5286
    | exact resolve eq5286 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5286
  have eq5410 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (k (σ (M.op x y)) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq5352
    | exact resolve eq5352 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5352
  have eq5415 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq5357
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5357
    | exact resolve eq5357 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5357
  have eq5457 : (k (σ (M.op x y)) (σ x)) = (M.op (k (σ (M.op x y)) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq5410
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5410
    | exact resolve eq5410 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5410
  have eq5461 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq5415
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5415
    | exact resolve eq5415 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5415
  have eq5495 : (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq5461
    | exact resolve eq5461 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5461
  have eq5649 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op (M.op X0 (M.op X0 y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq553 X0 sF0 sF0
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq553
    | exact resolve eq553 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq7307 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op (M.op X2 (M.op X2 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq547 X1 X2 (M.op X0 X1) X0 (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq547
    | exact resolve eq547 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq16193 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op (σ y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1181 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1181
    | exact resolve eq1181 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181
  have eq18462 : ∀ X0 : G, (M.op y (τ X0)) = (τ (M.op (σ y) X0)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq378 (τ X0)
       have i₂ := eq16193 X0
       grind)
    | exact superpose eq16193 eq378
    | exact resolve eq378 eq16193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq16193
  have eq18479 : ∀ X0 : G, (M.op y (τ X0)) = (τ (M.op (σ y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq18462 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18462
  have eq27755 : (M.op y (M.op x y)) = (τ (M.op (σ y) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq18479
    | exact resolve eq18479 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18479
  have eq27838 : (σ (M.op y (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27755 eq15
    | exact resolve eq15 eq27755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27755
  have eq50990 : y = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5649 y
       have i₂ := eq720
       grind)
    | exact superpose eq720 eq5649
    | exact resolve eq5649 eq720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720 eq5649
  have eq51065 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq50990 eq27838
    | exact resolve eq27838 eq50990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27838 eq50990
  have eq51121 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq51065
  have eq51132 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq51121
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq51121
    | exact resolve eq51121 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51121
  have eq51408 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (M.op X0 (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq51132 eq14
    | exact resolve eq14 eq51132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51132
  have eq71706 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq252 eq7307
    | exact resolve eq7307 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq190239 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq71706 eq51408
    | exact resolve eq51408 eq71706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51408 eq71706
  have eq190345 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq190239
  have eq190359 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq190345 eq955
    | exact resolve eq955 eq190345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955 eq190345
  have eq190442 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq190359
  have eq190446 : y = (M.op x y) := by
    first
    | (have r₁ := eq190442
       have r₂ := eq27
       grind)
    | exact resolve eq190442 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190442
  have eq190448 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq190446 eq20
    | exact resolve eq20 eq190446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190454 : y ≠ y ∨ x = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq190446 eq73
    | (have r₁ := eq73
       have r₂ := eq190446
       grind)
    | exact resolve eq73 eq190446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq190499 : y = (M.op y y) := by
    first
    | exact superpose eq190446 eq218
    | exact resolve eq218 eq190446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq190754 : x = (k y x) ∨ x = (M.op x x) := by grind
  clear eq190454
  have eq190885 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq190448
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq190448
    | exact resolve eq190448 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190448
  have eq191887 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq190885 eq26
    | exact resolve eq26 eq190885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq191988 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq190885 eq3550
    | exact resolve eq3550 eq190885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3550
  have eq192018 : (k (σ (M.op x y)) (σ x)) = (M.op (k (σ (M.op x y)) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq190885 eq5495
    | exact resolve eq5495 eq190885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5495
  have eq192316 : (k (σ (M.op x y)) (σ x)) = (M.op (k (σ (M.op x y)) (σ x)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq192018
       have r₂ := eq27
       grind)
    | exact resolve eq192018 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192018
  have eq192320 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq191988
       have r₂ := eq27
       grind)
    | exact resolve eq191988 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191988
  have eq192401 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq190499
       grind)
    | exact superpose eq190499 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq190499
       grind)
    | exact resolve eq13 eq190499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192448 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq192401 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192401
  have eq193789 : ∀ X0 : G, (M.op y (τ X0)) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq1104 X0
       have i₂ := eq192448 (τ X0)
       grind)
    | exact superpose eq192448 eq1104
    | exact resolve eq1104 eq192448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq193922 : ∀ X0 : G, (σ y) ≠ (σ (M.op y y)) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq469 y X0
       have i₂ := eq192448 y
       grind)
    | exact superpose eq192448 eq469
    | (have j0 := eq469 y X0
       grind)
    | exact resolve eq469 eq192448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq193934 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq2345 y
       have i₂ := eq192448 y
       grind)
    | exact superpose eq192448 eq2345
    | (have j0 := eq2345 y
       grind)
    | exact resolve eq2345 eq192448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2345 eq192448
  have eq194155 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq193934
       have i₂ := eq190499
       grind)
    | exact superpose eq190499 eq193934
    | exact resolve eq193934 eq190499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193934
  have eq194164 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq193922 X0
       have i₂ := eq190499
       grind)
    | exact superpose eq190499 eq193922
    | (have j0 := eq193922 X0
       grind)
    | exact resolve eq193922 eq190499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193922
  have eq194165 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq194164 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194164
  have eq194244 : ∀ X0 : G, (M.op y (τ X0)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq190885 eq193789
    | exact resolve eq193789 eq190885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193789
  have eq194339 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq194155
       have r₂ := eq24
       grind)
    | exact resolve eq194155 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194155
  have eq194348 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq194165 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq194165
    | (have j0 := eq194165 X0
       grind)
    | exact resolve eq194165 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194165
  have eq194456 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq190885 eq194339
    | exact resolve eq194339 eq190885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194339
  have eq194460 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq190885 eq194348
    | exact resolve eq194348 eq190885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194348
  have eq194542 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq194456
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq194456
    | exact resolve eq194456 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194456
  have eq194593 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq190885 eq194542
    | exact resolve eq194542 eq190885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194542
  have eq194782 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq194593 eq7307
    | exact resolve eq7307 eq194593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194788 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq194593 eq194782
    | exact resolve eq194782 eq194593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194593 eq194782
  have eq204226 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq5457 eq194788
    | exact resolve eq194788 eq5457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5457 eq194788
  have eq204377 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq191887 eq204226
    | exact resolve eq204226 eq191887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204226
  have eq204394 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ x))) := by
    first
    | (have r₁ := eq204377
       have r₂ := eq27
       grind)
    | exact resolve eq204377 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204377
  have eq207681 : ∀ X0 : G, (M.op y (τ X0)) = (τ (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq194460 eq194244
    | exact resolve eq194244 eq194460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194244 eq194460
  have eq208394 : (M.op y (k y x)) = (τ (M.op (σ (M.op x y)) (k (σ y) (σ x)))) := by
    first
    | exact superpose eq80 eq207681
    | exact resolve eq207681 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq207681
  have eq208478 : (M.op y (k y x)) = (τ (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ x)))) := by
    first
    | exact superpose eq190885 eq208394
    | exact resolve eq208394 eq190885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208394
  have eq208566 : (τ (σ (M.op x y))) = (M.op y (k y x)) := by
    first
    | exact superpose eq204394 eq208478
    | exact resolve eq208478 eq204394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204394 eq208478
  have eq208636 : (M.op x y) = (M.op y (k y x)) := by
    first
    | exact superpose eq30 eq208566
    | exact resolve eq208566 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq208566
  have eq208694 : y = (M.op y (k y x)) := by
    first
    | exact superpose eq190446 eq208636
    | exact resolve eq208636 eq190446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208636
  have eq208815 : ∀ X0 : G, (M.op y y) = (M.op (M.op y y) (M.op X0 (k y x))) := by
    intro X0
    first
    | (have i₁ := eq7307 X0 (k y x) y
       have i₂ := eq208694
       grind)
    | exact superpose eq208694 eq7307
    | exact resolve eq7307 eq208694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7307 eq208694
  have eq208819 : ∀ X0 : G, y = (M.op y (M.op X0 (k y x))) := by
    intro X0
    first
    | (have i₁ := eq208815 X0
       have i₂ := eq190499
       grind)
    | exact superpose eq190499 eq208815
    | exact resolve eq208815 eq190499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208815
  have eq208834 : (σ (k y (k y x))) = (M.op (k (σ (M.op x y)) (σ x)) (σ (M.op x y))) ∨ (σ y) = (M.op (k (σ y) (σ x)) (σ y)) := by
    first
    | exact superpose eq190885 eq2324
    | exact resolve eq2324 eq190885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2324
  have eq208835 : (σ (k y (k y x))) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (k (σ y) (σ x)) (σ y)) := by
    first
    | exact superpose eq192316 eq208834
    | exact resolve eq208834 eq192316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208834
  have eq208836 : (k (σ y) (k (σ y) (σ x))) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (k (σ y) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq208835
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq208835
    | exact resolve eq208835 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq208835
  have eq208837 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (k (σ (M.op x y)) (σ x))) ∨ (σ y) = (M.op (k (σ y) (σ x)) (σ y)) := by
    first
    | exact superpose eq190885 eq208836
    | exact resolve eq208836 eq190885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208836
  have eq208838 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ x)) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq190885 eq208837
    | exact resolve eq208837 eq190885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208837
  have eq208839 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq192316 eq208838
    | exact resolve eq208838 eq192316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192316 eq208838
  have eq208840 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (k (σ (M.op x y)) (σ x))) := by
    first
    | (have r₁ := eq208839
       have r₂ := eq192320
       grind)
    | exact resolve eq208839 eq192320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208839
  have eq208848 : (M.op (σ x) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ x) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq208840
       have i₂ := eq91 sF1 sF2
       grind)
    | exact superpose eq91 eq208840
    | (have j1 := eq91 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq208840 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq208840
  have eq208864 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq191887 eq208848
    | exact resolve eq208848 eq191887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208848
  have eq208867 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq191887 eq208864
    | exact resolve eq208864 eq191887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208864
  have eq208869 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq208867
       have r₂ := eq27
       grind)
    | exact resolve eq208867 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208867
  have eq211461 : (k y x) = (M.op (k y x) (M.op y y)) := by
    first
    | (have i₁ := eq243 y x (k y x)
       have i₂ := eq208819 x
       grind)
    | exact superpose eq208819 eq243
    | exact resolve eq243 eq208819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243 eq208819
  have eq211551 : (k y x) = (M.op (k y x) y) := by
    first
    | (have i₁ := eq211461
       have i₂ := eq190499
       grind)
    | exact superpose eq190499 eq211461
    | exact resolve eq211461 eq190499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190499 eq211461
  have eq214031 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2343 x
       have i₂ := eq190754
       grind)
    | exact superpose eq190754 eq2343
    | (have j0 := eq2343 x
       grind)
    | exact resolve eq2343 eq190754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2343 eq190754
  have eq214052 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq190885 eq214031
    | exact resolve eq214031 eq190885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214031
  have eq214086 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq214052
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq214052
    | exact resolve eq214052 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214052
  have eq214117 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq191887 eq214086
    | exact resolve eq214086 eq191887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214086
  have eq214136 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq190885 eq214117
    | exact resolve eq214117 eq190885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214117
  have eq214152 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq214136
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq214136
    | exact resolve eq214136 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214136
  have eq214165 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq191887 eq214152
    | exact resolve eq214152 eq191887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191887 eq214152
  have eq214175 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq214165
       have r₂ := eq27
       grind)
    | exact resolve eq214165 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214165
  have eq214195 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq214175
       grind)
    | exact superpose eq214175 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq214175
       grind)
    | exact resolve eq13 eq214175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214175
  have eq214242 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq214195 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214195
  have eq221072 : (k (σ (M.op x y)) (σ x)) = (σ (M.op x (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq136
       have i₂ := eq214242 sF0
       grind)
    | exact superpose eq214242 eq136
    | exact resolve eq136 eq214242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq214242
  have eq221369 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq190446 eq221072
    | exact resolve eq221072 eq190446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221072
  have eq221517 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq221369
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq221369
    | exact resolve eq221369 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221369
  have eq221622 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq221517
    | exact resolve eq221517 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq221517
  have eq221711 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq221622
       have r₂ := eq192320
       grind)
    | exact resolve eq221622 eq192320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192320 eq221622
  have eq221817 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq221711 eq27
    | exact resolve eq27 eq221711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq221885 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq221711 eq208869
    | exact resolve eq208869 eq221711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208869 eq221711
  have eq221982 : (τ (σ x)) = (k (M.op x y) x) := by
    first
    | exact superpose eq221885 eq147
    | exact resolve eq147 eq221885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq221885
  have eq222035 : (τ (σ x)) = (k y x) := by
    first
    | exact superpose eq190446 eq221982
    | exact resolve eq221982 eq190446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221982
  have eq222044 : x = (k y x) := by
    first
    | exact superpose eq28 eq222035
    | exact resolve eq222035 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq222035
  have eq222149 : x = (M.op x y) := by
    first
    | (have i₁ := eq211551
       have i₂ := eq222044
       grind)
    | exact superpose eq222044 eq211551
    | exact resolve eq211551 eq222044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211551 eq222044
  have eq222186 : x = (M.op x y) := by
    first
    | (have i₁ := eq222149
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq222149
    | exact resolve eq222149 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq222149
  have eq222223 : x = y := by
    first
    | exact superpose eq190446 eq222186
    | exact resolve eq222186 eq190446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190446 eq222186
  have eq222303 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq222223
       grind)
    | exact superpose eq222223 eq24
    | exact resolve eq24 eq222223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq222223
  have eq223186 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq190885 eq222303
    | exact resolve eq222303 eq190885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190885 eq222303
  have eq223560 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq223186
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq223186
    | exact resolve eq223186 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq223186
  have eq223849 : False := by grind
  exact eq223849
