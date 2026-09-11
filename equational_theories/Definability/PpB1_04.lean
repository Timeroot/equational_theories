import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1446`: `x = (x ◇ y) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_x_pxy_pxx_pxy_Equation1446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X2))) = X0 := by
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
  clear eq25 eq36
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
  have eq51 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) X0))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op X0 (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X0 X2) (M.op X0 (M.op X2 x))
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X1) X0 (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq83
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq83
    | exact resolve eq83 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq91
    | exact resolve eq91 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq206 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op X0 x)) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) := by
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 (M.op X0 X1) (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : (M.op x y) = (M.op x (M.op (M.op x y) x)) := by
    first
    | exact superpose eq51 eq56
    | exact resolve eq56 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq367 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq52 eq56
    | exact resolve eq56 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq381 : x = (M.op (M.op x y) (M.op x (M.op x y))) := by
    first
    | exact superpose eq366 eq56
    | exact resolve eq56 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq367 eq56
    | exact resolve eq56 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq52 eq57
    | exact resolve eq57 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq431 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq412 eq56
    | exact resolve eq56 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq412
  have eq549 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq76 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq550 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq549 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq3774 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq550 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq550
    | (have j0 := eq550 (τ X0)
       grind)
    | exact resolve eq550 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq550
  have eq3782 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3774 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3774
    | (have j0 := eq3774 X0
       grind)
    | exact resolve eq3774 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3774
  have eq3788 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3782 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3782
    | (have j0 := eq3782 X0
       grind)
    | exact resolve eq3782 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3782
  have eq24157 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq92 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24165 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq24157
    | exact resolve eq24157 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24157
  have eq24176 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq24165
       have r₂ := eq28
       grind)
    | exact resolve eq24165 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24165
  have eq24185 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq24176
  have eq24225 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq24185
    | exact resolve eq24185 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24185
  have eq24401 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq24225 eq92
    | exact resolve eq92 eq24225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq24225
  have eq24417 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq24401
  have eq24420 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq24417
       have r₂ := eq28
       grind)
    | exact resolve eq24417 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24417
  have eq24432 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  have eq24682 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq24432 eq50
    | exact resolve eq50 eq24432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24432
  have eq29021 : (τ (σ x)) = (k x x) ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq24420 eq24682
    | exact resolve eq24682 eq24420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24420 eq24682
  have eq29077 : (τ (σ x)) = (k x x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq29021
  have eq29086 : x = (k x x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq29077
    | exact resolve eq29077 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29077
  have eq29087 : x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq3788 x
       grind)
    | (have r₁ := eq29086
       have r₂ := eq3788 x
       grind)
    | exact resolve eq29086 eq3788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29086
  have eq29101 : (M.op x y) = (k x y) ∨ x = (M.op x x) := by grind
  clear eq29087
  have eq29151 : (M.op x y) = (k x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq29101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29101
    | exact resolve eq29101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq29101
  have eq29264 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq29151
       grind)
    | exact superpose eq29151 eq45
    | exact resolve eq45 eq29151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq29151
  have eq29298 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq29264
    | exact resolve eq29264 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29264
  have eq29342 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29298 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq29298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29352 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq29342
    | exact resolve eq29342 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29342
  have eq29363 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq29352
       have r₂ := eq28
       grind)
    | exact resolve eq29352 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29352
  have eq30795 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq29363
  have eq30839 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq30795
    | exact resolve eq30795 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq30795
  have eq30962 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30839 eq29298
    | exact resolve eq29298 eq30839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29298 eq30839
  have eq30972 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq30962
  have eq30991 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq30972
       have r₂ := eq28
       grind)
    | exact resolve eq30972 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30972
  have eq31006 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30991 eq211
    | exact resolve eq211 eq30991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31135 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq31006 eq57
    | exact resolve eq57 eq31006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31006
  have eq31420 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq31135 eq387
    | exact resolve eq387 eq31135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31135
  have eq31483 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30991 eq31420
    | exact resolve eq31420 eq30991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31420
  have eq31537 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq31483
  have eq31538 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq31537 eq210
    | exact resolve eq210 eq31537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31537
  have eq31601 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq31538 eq30991
    | exact resolve eq30991 eq31538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31538
  have eq31656 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq31601
  have eq31676 : (k x x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq31995 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq31676
       grind)
    | exact superpose eq31676 eq44
    | exact resolve eq44 eq31676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq31676
  have eq33198 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31995
       have i₂ := eq31656
       grind)
    | exact superpose eq31656 eq31995
    | exact resolve eq31995 eq31656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31656 eq31995
  have eq33275 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq33198
  have eq33282 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33275
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq33275
    | exact resolve eq33275 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33275
  have eq33396 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33282 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq33282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33282
  have eq33411 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq33396
  have eq33445 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33411 eq211
    | exact resolve eq211 eq33411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq33822 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33445 eq57
    | exact resolve eq57 eq33445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq33445
  have eq34305 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33822 eq387
    | exact resolve eq387 eq33822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387 eq33822
  have eq34386 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33411 eq34305
    | exact resolve eq34305 eq33411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34305
  have eq34440 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq34386
  have eq34442 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34440 eq210
    | exact resolve eq210 eq34440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq34440
  have eq34552 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34442 eq33411
    | exact resolve eq33411 eq34442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33411 eq34442
  have eq34609 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq34552
  have eq34619 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq34609 eq28
    | exact resolve eq28 eq34609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq34621 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op X0 (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq34609 eq55
    | exact resolve eq55 eq34609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq34626 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq34609 eq367
    | exact resolve eq367 eq34609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq35107 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq431 eq34621
    | exact resolve eq34621 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq35196 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq34609 eq35107
    | exact resolve eq35107 eq34609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34609 eq35107
  have eq35202 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq34621 eq35196
    | exact resolve eq35196 eq34621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34621 eq35196
  have eq35571 : (k (σ x) (M.op (σ x) (σ x))) = (M.op (σ x) (M.op (σ x) (σ x))) := by grind
  clear eq35202
  have eq35608 : (σ x) = (k (σ x) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq34626 eq35571
    | exact resolve eq35571 eq34626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34626 eq35571
  have eq35701 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30991 eq35608
    | exact resolve eq35608 eq30991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30991 eq35608
  have eq36567 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq35701 eq50
    | exact resolve eq50 eq35701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq35701
  have eq36621 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq36567
    | exact resolve eq36567 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq36567
  have eq36624 : x = (M.op x x) := by
    first
    | (have j1 := eq3788 x
       grind)
    | (have r₁ := eq36621
       have r₂ := eq3788 x
       grind)
    | exact resolve eq36621 eq3788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3788 eq36621
  have eq36692 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq206 x
       have i₂ := eq36624
       grind)
    | exact superpose eq36624 eq206
    | exact resolve eq206 eq36624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq37190 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq36692 eq362
    | exact resolve eq362 eq36692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362 eq36692
  have eq37264 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq37190
       have i₂ := eq36624
       grind)
    | exact superpose eq36624 eq37190
    | exact resolve eq37190 eq36624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37190
  have eq37269 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq37264 eq381
    | exact resolve eq381 eq37264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381 eq37264
  have eq37504 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq37269 eq366
    | exact resolve eq366 eq37269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366 eq37269
  have eq37569 : x = (M.op x y) := by
    first
    | (have i₁ := eq37504
       have i₂ := eq36624
       grind)
    | exact superpose eq36624 eq37504
    | exact resolve eq37504 eq36624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36624 eq37504
  have eq37571 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq37569 eq21
    | exact resolve eq21 eq37569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq37569
  have eq37780 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq37571
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37571
    | exact resolve eq37571 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq37571
  have eq37810 : False := by grind
  exact eq37810

/-- `Equation1446`: `x = (x ◇ y) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_pyx_pxy_Equation1446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq63 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X0 X2) (M.op X0 (M.op X2 x))
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 (M.op X0 X1) (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq64 (M.op X0 X1) (M.op X0 (M.op X1 x))
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq63 (M.op X0 X1) X0 X0
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq63
    | exact resolve eq63 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq483 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = X1 ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq29
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq486 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq734 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq478 x y
       grind)
    | exact superpose eq478 eq16
    | (have j1 := eq478 x y
       grind)
    | exact resolve eq16 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq754 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq756 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq478 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq756 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq758 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq754 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq760 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq758 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq758
    | (have j0 := eq758 X0
       grind)
    | exact resolve eq758 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq4234 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq486 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq486
    | exact resolve eq486 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq4281 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4234 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4234
    | (have j0 := eq4234 X0 X1
       grind)
    | exact resolve eq4234 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4234
  have eq4434 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    grind
  clear eq760
  have eq4436 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq4434 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq4434
    | (have j0 := eq4434 X0
       grind)
    | exact resolve eq4434 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4434
  have eq4570 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq483 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq483
    | exact resolve eq483 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq4657 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4570 X0 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq4570
    | (have j0 := eq4570 X0 X1
       grind)
    | exact resolve eq4570 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4570
  have eq4689 : ∀ X0 X1 X2 : G, (k (k X0 X1) (σ X2)) = (σ (k (τ (M.op X0 X1)) X2)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 (k X0 X1) X2
       have i₂ := eq4657 X0 X1
       grind)
    | exact superpose eq4657 eq18
    | (have j1 := eq4657 X0 X1
       grind)
    | exact resolve eq18 eq4657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4657
  have eq4797 : ∀ X0 X1 X2 : G, (k (k X0 X1) (σ X2)) = (k (M.op X0 X1) (σ X2)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4689 X0 X1 X2
       have i₂ := eq18 (M.op X0 X1) X2
       grind)
    | exact superpose eq18 eq4689
    | (have j0 := eq4689 X0 X1 X2
       grind)
    | exact resolve eq4689 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4689
  have eq15772 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    grind
  clear eq4436
  have eq15850 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq15772 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq15772
    | (have j0 := eq15772 X0
       grind)
    | exact resolve eq15772 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15772
  have eq15851 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq15850 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15850
  have eq15882 : ∀ X0 : G, (σ (k (σ (k X0 X0)) (σ X0))) = (M.op (σ (σ (k X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15851 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq15851
    | exact resolve eq15851 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15901 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (k X0 (σ (τ X0))) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq15851 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq15851
    | exact resolve eq15851 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16003 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq15901 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15901
    | exact resolve eq15901 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15901
  have eq16015 : ∀ X0 : G, (σ (σ (k (k X0 X0) X0))) = (M.op (σ (σ (k X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15882 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq15882
    | exact resolve eq15882 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15882
  have eq16033 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k (σ (k (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq16003 X0
       have i₂ := eq19 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq19 eq16003
    | exact resolve eq16003 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16003
  have eq16055 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k (k (σ (τ X0)) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq16033 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq16033
    | exact resolve eq16033 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16033
  have eq16072 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq16055 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16055
    | exact resolve eq16055 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16055
  have eq16123 : ∀ X0 : G, (k (τ (k X0 X0)) (τ X0)) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq16072 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq16072
    | exact resolve eq16072 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16146 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (M.op (k (σ X0) (σ X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4797 (σ X0) (σ X0) X0
       have i₂ := eq16072 (σ X0)
       grind)
    | exact superpose eq16072 eq4797
    | (have j0 := eq4797 (σ X0) (σ X0) x
       grind)
    | exact resolve eq4797 eq16072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4797
  have eq16197 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (M.op (k (σ X0) (σ X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq16146 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16146
  have eq16245 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16197 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq16197
    | (have j0 := eq16197 X0
       grind)
    | exact resolve eq16197 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16197
  have eq16265 : ∀ X0 : G, (M.op (τ (k X0 X0)) (τ X0)) = (τ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq16123 X0
       have i₂ := eq32 X0 (k X0 X0)
       grind)
    | exact superpose eq32 eq16123
    | exact resolve eq16123 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16123
  have eq16312 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16245 X0
       have i₂ := eq15851 X0
       grind)
    | exact superpose eq15851 eq16245
    | (have j0 := eq16245 X0
       grind)
    | exact resolve eq16245 eq15851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15851 eq16245
  have eq16326 : ∀ X0 : G, (M.op (τ (k X0 X0)) (τ X0)) = (τ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq16265 X0
       have i₂ := eq16072 X0
       grind)
    | exact superpose eq16072 eq16265
    | exact resolve eq16265 eq16072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16265
  have eq16367 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16312 X0
       have i₂ := eq16072 X0
       grind)
    | exact superpose eq16072 eq16312
    | (have j0 := eq16312 X0
       grind)
    | exact resolve eq16312 eq16072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16312
  have eq16403 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq16367
  have eq17551 : ∀ X0 : G, (σ (σ (k (σ (k X0 X0)) (σ X0)))) = (M.op (σ (σ (σ (k X0 X0)))) (σ (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq16015 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq16015
    | exact resolve eq16015 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16015
  have eq17761 : ∀ X0 : G, (σ (σ (σ (k (k X0 X0) X0)))) = (M.op (σ (σ (σ (k X0 X0)))) (σ (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq17551 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq17551
    | exact resolve eq17551 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17551
  have eq17799 : ∀ X0 : G, (σ (σ (σ (M.op (k X0 X0) X0)))) = (M.op (σ (σ (σ (k X0 X0)))) (σ (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq17761 X0
       have i₂ := eq16072 X0
       grind)
    | exact superpose eq16072 eq17761
    | exact resolve eq17761 eq16072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16072 eq17761
  have eq21492 : ∀ X0 : G, (σ (σ (σ (M.op (k (τ X0) (τ X0)) (τ X0))))) = (M.op (σ (σ (k X0 (σ (τ X0))))) (σ (σ (σ (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq17799 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq17799
    | exact resolve eq17799 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17799
  have eq21604 : ∀ X0 : G, (M.op (σ (σ (k X0 X0))) (σ (σ X0))) = (σ (σ (σ (M.op (k (τ X0) (τ X0)) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq21492 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21492
    | exact resolve eq21492 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21492
  have eq21640 : ∀ X0 : G, (M.op (σ (σ (k X0 X0))) (σ (σ X0))) = (σ (σ (σ (M.op (τ (k X0 X0)) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq21604 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq21604
    | exact resolve eq21604 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21604
  have eq21666 : ∀ X0 : G, (M.op (σ (σ (k X0 X0))) (σ (σ X0))) = (σ (σ (σ (τ (M.op (k X0 X0) X0))))) := by
    intro X0
    first
    | (have i₁ := eq21640 X0
       have i₂ := eq16326 X0
       grind)
    | exact superpose eq16326 eq21640
    | exact resolve eq21640 eq16326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21640
  have eq21687 : ∀ X0 : G, (σ (σ (M.op (k X0 X0) X0))) = (M.op (σ (σ (k X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq21666 X0
       have i₂ := eq11 (M.op (k X0 X0) X0)
       grind)
    | exact superpose eq11 eq21666
    | exact resolve eq21666 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21666
  have eq21751 : ∀ X0 : G, (M.op (σ (σ (k (τ X0) (τ X0)))) (σ X0)) = (σ (σ (M.op (k (τ X0) (τ X0)) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq21687 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21687
    | exact resolve eq21687 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21687
  have eq21861 : ∀ X0 : G, (σ (σ (M.op (τ (k X0 X0)) (τ X0)))) = (M.op (σ (σ (τ (k X0 X0)))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq21751 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq21751
    | exact resolve eq21751 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21751
  have eq21896 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (σ (M.op (τ (k X0 X0)) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq21861 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq21861
    | exact resolve eq21861 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21861
  have eq21922 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (σ (τ (M.op (k X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq21896 X0
       have i₂ := eq16326 X0
       grind)
    | exact superpose eq16326 eq21896
    | exact resolve eq21896 eq16326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21896
  have eq21942 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq21922 X0
       have i₂ := eq11 (M.op (k X0 X0) X0)
       grind)
    | exact superpose eq11 eq21922
    | exact resolve eq21922 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21922
  have eq34374 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (M.op (k X0 X0) X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq64 (σ X0) (σ X0)
       have i₂ := eq16403 X0
       grind)
    | exact superpose eq16403 eq64
    | (have j1 := eq16403 X0
       grind)
    | exact resolve eq64 eq16403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq34375 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ (M.op (k X0 X0) X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq69 (σ X0) (σ X0)
       have i₂ := eq16403 X0
       grind)
    | exact superpose eq16403 eq69
    | (have j1 := eq16403 X0
       grind)
    | exact resolve eq69 eq16403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq16403
  have eq35679 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (M.op (k (τ X0) (τ X0)) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34374 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq34374
    | exact resolve eq34374 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34374
  have eq35826 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (M.op (τ (k X0 X0)) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq35679 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq35679
    | (have j0 := eq35679 X0
       grind)
    | exact resolve eq35679 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35679
  have eq35853 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (τ (M.op (k X0 X0) X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq35826 X0
       have i₂ := eq16326 X0
       grind)
    | exact superpose eq16326 eq35826
    | (have j0 := eq35826 X0
       grind)
    | exact resolve eq35826 eq16326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35826
  have eq35873 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (k X0 X0) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq35853 X0
       have i₂ := eq11 (M.op (k X0 X0) X0)
       grind)
    | exact superpose eq11 eq35853
    | (have j0 := eq35853 X0
       grind)
    | exact resolve eq35853 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35853
  have eq36721 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq734
       have i₂ := eq4281 x y
       grind)
    | exact superpose eq4281 eq734
    | (have j1 := eq4281 (σ x) (σ y)
       grind)
    | (have r₁ := eq734
       have r₂ := eq4281 x y
       grind)
    | exact resolve eq734 eq4281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734 eq4281
  have eq36722 : y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq36721
  have eq39192 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ (M.op (k (τ X0) (τ X0)) (τ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34375 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq34375
    | exact resolve eq34375 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34375
  have eq39336 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ (M.op (τ (k X0 X0)) (τ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq39192 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq39192
    | (have j0 := eq39192 X0
       grind)
    | exact resolve eq39192 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq39192
  have eq39349 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ (τ (M.op (k X0 X0) X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq39336 X0
       have i₂ := eq16326 X0
       grind)
    | exact superpose eq16326 eq39336
    | (have j0 := eq39336 X0
       grind)
    | exact resolve eq39336 eq16326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16326 eq39336
  have eq39358 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq39349 X0
       have i₂ := eq11 (M.op (k X0 X0) X0)
       grind)
    | exact superpose eq11 eq39349
    | (have j0 := eq39349 X0
       grind)
    | exact resolve eq39349 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39349
  have eq39392 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq63 (k X0 X0) X0 X0
       have i₂ := eq39358 X0
       grind)
    | exact superpose eq39358 eq63
    | (have j1 := eq39358 X0
       grind)
    | exact resolve eq63 eq39358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq39358
  have eq39638 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) (k (σ X0) (σ X0)))) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39392 (σ x)
       have i₂ := eq478 x x
       grind)
    | exact superpose eq478 eq39392
    | (have j0 := eq39392 (σ X0)
       have j1 := eq478 X0 X0
       grind)
    | exact resolve eq39392 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478 eq39392
  have eq39735 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) (k (σ X0) (σ X0)))) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq39638 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39638
  have eq39746 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) (k (σ X0) (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq39735 X0
       have j1 := eq757 X0
       grind)
    | (have r₁ := eq39735 X0
       have r₂ := eq757 X0
       grind)
    | exact resolve eq39735 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757 eq39735
  have eq39750 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39746 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq39746
    | (have j0 := eq39746 X0
       grind)
    | exact resolve eq39746 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39746
  have eq45002 : ∀ X0 : G, (σ (τ X0)) = (M.op (k X0 (σ (τ X0))) (M.op (σ (τ X0)) (k X0 (σ (τ X0))))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq39750 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq39750
    | (have j0 := eq39750 (τ X0)
       grind)
    | exact resolve eq39750 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq39750
  have eq45121 : ∀ X0 : G, (M.op (k X0 X0) (M.op X0 (k X0 X0))) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq45002 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq45002
    | (have j0 := eq45002 X0
       grind)
    | exact resolve eq45002 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45002
  have eq45177 : ∀ X0 : G, (M.op (k X0 X0) (M.op X0 (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq45121 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq45121
    | (have j0 := eq45121 X0
       grind)
    | exact resolve eq45121 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45121
  have eq45277 : ∀ X0 : G, (k X0 X0) = (M.op (M.op (k X0 X0) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq76 (k X0 X0) (M.op X0 (k X0 X0))
       have i₂ := eq45177 X0
       grind)
    | exact superpose eq45177 eq76
    | (have j1 := eq45177 X0
       grind)
    | exact resolve eq76 eq45177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45177
  have eq46341 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq35873 X0
       have i₂ := eq45277 X0
       grind)
    | exact superpose eq45277 eq35873
    | (have j0 := eq35873 X0
       have j1 := eq45277 X0
       grind)
    | exact resolve eq35873 eq45277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35873 eq45277
  have eq46483 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq46341 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46341
  have eq46921 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq46483 (σ X0)
       grind)
    | exact superpose eq46483 eq15
    | (have j1 := eq46483 (σ X0)
       grind)
    | exact resolve eq15 eq46483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46483
  have eq49176 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  clear eq46921
  have eq49241 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq49176 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq49176
    | (have j0 := eq49176 X0
       grind)
    | exact resolve eq49176 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49176
  have eq49242 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq49241 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49241
  have eq49319 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq49242 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq49242
    | exact resolve eq49242 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49633 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq49319 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq49319
    | exact resolve eq49319 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq49319
  have eq49712 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq49633 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq49633
    | exact resolve eq49633 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49633
  have eq49961 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq21942 X0
       have i₂ := eq49712 X0
       grind)
    | exact superpose eq49712 eq21942
    | exact resolve eq21942 eq49712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21942
  have eq678965 : x = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq89 x y
       have i₂ := eq36722
       grind)
    | exact superpose eq36722 eq89
    | exact resolve eq89 eq36722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq679102 : (σ x) = (σ (k y y)) ∨ x = (M.op y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq678965
       have i₂ := eq49242 y
       grind)
    | exact superpose eq49242 eq678965
    | exact resolve eq678965 eq49242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678965
  have eq679191 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq679102
       have i₂ := eq49712 y
       grind)
    | exact superpose eq49712 eq679102
    | exact resolve eq679102 eq49712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679102
  have eq1495049 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq679191
       have i₂ := eq36722
       grind)
    | exact superpose eq36722 eq679191
    | exact resolve eq679191 eq36722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36722 eq679191
  have eq1495202 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1495049
  have eq1495244 : (σ x) = (σ (k y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1495202
       have i₂ := eq49242 y
       grind)
    | exact superpose eq49242 eq1495202
    | exact resolve eq1495202 eq49242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1495202
  have eq1495245 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1495244
       have i₂ := eq49712 y
       grind)
    | exact superpose eq49712 eq1495244
    | exact resolve eq1495244 eq49712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1495244
  have eq1495246 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1495245
  have eq1495340 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq76 (σ x) (σ y)
       have i₂ := eq1495246
       grind)
    | exact superpose eq1495246 eq76
    | exact resolve eq76 eq1495246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq1506423 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1495340
       have i₂ := eq1495246
       grind)
    | exact superpose eq1495246 eq1495340
    | exact resolve eq1495340 eq1495246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1495246 eq1495340
  have eq1506611 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1506423
  have eq1506664 : (σ x) = (σ (k y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1506611
       have i₂ := eq49242 y
       grind)
    | exact superpose eq49242 eq1506611
    | exact resolve eq1506611 eq49242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49242 eq1506611
  have eq1506695 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1506664
       have i₂ := eq49712 y
       grind)
    | exact superpose eq49712 eq1506664
    | exact resolve eq1506664 eq49712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49712 eq1506664
  have eq1506696 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq1506695
  have eq1506856 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1506696
       grind)
    | exact superpose eq1506696 eq10
    | exact resolve eq10 eq1506696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1506696
  have eq1507458 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1506856
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1506856
    | exact resolve eq1506856 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1506856
  have eq1507459 : x = (M.op y y) := by grind
  clear eq1507458
  have eq1507815 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq49961 y
       have i₂ := eq1507459
       grind)
    | exact superpose eq1507459 eq49961
    | exact resolve eq49961 eq1507459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49961 eq1507459
  have eq1508385 : False := by grind
  exact eq1508385

/-- `Equation1446`: `x = (x ◇ y) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_pyy_pxy_Equation1446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq63 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X0 X2) (M.op X0 (M.op X2 x))
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 (M.op X0 X1) (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq64 (M.op X0 X1) (M.op X0 (M.op X1 x))
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq63 (M.op X0 X1) X0 X0
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq63
    | exact resolve eq63 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq468 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq473 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = X1 ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq29
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq476 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq720 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq468 x y
       grind)
    | exact superpose eq468 eq16
    | (have j1 := eq468 x y
       grind)
    | exact resolve eq16 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq740 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq742 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq468 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq743 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq742 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq744 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq740 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq746 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq744 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq744
    | (have j0 := eq744 X0
       grind)
    | exact resolve eq744 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq4207 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq476 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq476
    | exact resolve eq476 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq4254 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4207 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4207
    | (have j0 := eq4207 X0 X1
       grind)
    | exact resolve eq4207 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4207
  have eq4407 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    grind
  clear eq746
  have eq4409 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq4407 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq4407
    | (have j0 := eq4407 X0
       grind)
    | exact resolve eq4407 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4407
  have eq4543 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq473 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq473
    | exact resolve eq473 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq4630 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4543 X0 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq4543
    | (have j0 := eq4543 X0 X1
       grind)
    | exact resolve eq4543 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4543
  have eq4662 : ∀ X0 X1 X2 : G, (k (k X0 X1) (σ X2)) = (σ (k (τ (M.op X0 X1)) X2)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 (k X0 X1) X2
       have i₂ := eq4630 X0 X1
       grind)
    | exact superpose eq4630 eq18
    | (have j1 := eq4630 X0 X1
       grind)
    | exact resolve eq18 eq4630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4630
  have eq4770 : ∀ X0 X1 X2 : G, (k (k X0 X1) (σ X2)) = (k (M.op X0 X1) (σ X2)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4662 X0 X1 X2
       have i₂ := eq18 (M.op X0 X1) X2
       grind)
    | exact superpose eq18 eq4662
    | (have j0 := eq4662 X0 X1 X2
       grind)
    | exact resolve eq4662 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4662
  have eq15741 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    grind
  clear eq4409
  have eq15819 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq15741 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq15741
    | (have j0 := eq15741 X0
       grind)
    | exact resolve eq15741 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15741
  have eq15820 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq15819 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15819
  have eq15851 : ∀ X0 : G, (σ (k (σ (k X0 X0)) (σ X0))) = (M.op (σ (σ (k X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15820 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq15820
    | exact resolve eq15820 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15870 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (k X0 (σ (τ X0))) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq15820 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq15820
    | exact resolve eq15820 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15972 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq15870 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15870
    | exact resolve eq15870 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15870
  have eq15984 : ∀ X0 : G, (σ (σ (k (k X0 X0) X0))) = (M.op (σ (σ (k X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15851 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq15851
    | exact resolve eq15851 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15851
  have eq16002 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k (σ (k (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq15972 X0
       have i₂ := eq19 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq19 eq15972
    | exact resolve eq15972 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15972
  have eq16024 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k (k (σ (τ X0)) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq16002 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq16002
    | exact resolve eq16002 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16002
  have eq16041 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq16024 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16024
    | exact resolve eq16024 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16024
  have eq16092 : ∀ X0 : G, (k (τ (k X0 X0)) (τ X0)) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq16041 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq16041
    | exact resolve eq16041 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16115 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (M.op (k (σ X0) (σ X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4770 (σ X0) (σ X0) X0
       have i₂ := eq16041 (σ X0)
       grind)
    | exact superpose eq16041 eq4770
    | (have j0 := eq4770 (σ X0) (σ X0) x
       grind)
    | exact resolve eq4770 eq16041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4770
  have eq16166 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (M.op (k (σ X0) (σ X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq16115 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16115
  have eq16214 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16166 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq16166
    | (have j0 := eq16166 X0
       grind)
    | exact resolve eq16166 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16166
  have eq16234 : ∀ X0 : G, (M.op (τ (k X0 X0)) (τ X0)) = (τ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq16092 X0
       have i₂ := eq32 X0 (k X0 X0)
       grind)
    | exact superpose eq32 eq16092
    | exact resolve eq16092 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16092
  have eq16281 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16214 X0
       have i₂ := eq15820 X0
       grind)
    | exact superpose eq15820 eq16214
    | (have j0 := eq16214 X0
       grind)
    | exact resolve eq16214 eq15820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15820 eq16214
  have eq16295 : ∀ X0 : G, (M.op (τ (k X0 X0)) (τ X0)) = (τ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq16234 X0
       have i₂ := eq16041 X0
       grind)
    | exact superpose eq16041 eq16234
    | exact resolve eq16234 eq16041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16234
  have eq16336 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16281 X0
       have i₂ := eq16041 X0
       grind)
    | exact superpose eq16041 eq16281
    | (have j0 := eq16281 X0
       grind)
    | exact resolve eq16281 eq16041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16281
  have eq16372 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq16336
  have eq17516 : ∀ X0 : G, (σ (σ (k (σ (k X0 X0)) (σ X0)))) = (M.op (σ (σ (σ (k X0 X0)))) (σ (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq15984 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq15984
    | exact resolve eq15984 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15984
  have eq17726 : ∀ X0 : G, (σ (σ (σ (k (k X0 X0) X0)))) = (M.op (σ (σ (σ (k X0 X0)))) (σ (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq17516 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq17516
    | exact resolve eq17516 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17516
  have eq17764 : ∀ X0 : G, (σ (σ (σ (M.op (k X0 X0) X0)))) = (M.op (σ (σ (σ (k X0 X0)))) (σ (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq17726 X0
       have i₂ := eq16041 X0
       grind)
    | exact superpose eq16041 eq17726
    | exact resolve eq17726 eq16041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16041 eq17726
  have eq21450 : ∀ X0 : G, (σ (σ (σ (M.op (k (τ X0) (τ X0)) (τ X0))))) = (M.op (σ (σ (k X0 (σ (τ X0))))) (σ (σ (σ (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq17764 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq17764
    | exact resolve eq17764 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17764
  have eq21562 : ∀ X0 : G, (M.op (σ (σ (k X0 X0))) (σ (σ X0))) = (σ (σ (σ (M.op (k (τ X0) (τ X0)) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq21450 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21450
    | exact resolve eq21450 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21450
  have eq21598 : ∀ X0 : G, (M.op (σ (σ (k X0 X0))) (σ (σ X0))) = (σ (σ (σ (M.op (τ (k X0 X0)) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq21562 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq21562
    | exact resolve eq21562 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21562
  have eq21624 : ∀ X0 : G, (M.op (σ (σ (k X0 X0))) (σ (σ X0))) = (σ (σ (σ (τ (M.op (k X0 X0) X0))))) := by
    intro X0
    first
    | (have i₁ := eq21598 X0
       have i₂ := eq16295 X0
       grind)
    | exact superpose eq16295 eq21598
    | exact resolve eq21598 eq16295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21598
  have eq21645 : ∀ X0 : G, (σ (σ (M.op (k X0 X0) X0))) = (M.op (σ (σ (k X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq21624 X0
       have i₂ := eq11 (M.op (k X0 X0) X0)
       grind)
    | exact superpose eq11 eq21624
    | exact resolve eq21624 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21624
  have eq21709 : ∀ X0 : G, (M.op (σ (σ (k (τ X0) (τ X0)))) (σ X0)) = (σ (σ (M.op (k (τ X0) (τ X0)) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq21645 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21645
    | exact resolve eq21645 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21645
  have eq21819 : ∀ X0 : G, (σ (σ (M.op (τ (k X0 X0)) (τ X0)))) = (M.op (σ (σ (τ (k X0 X0)))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq21709 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq21709
    | exact resolve eq21709 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21709
  have eq21854 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (σ (M.op (τ (k X0 X0)) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq21819 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq21819
    | exact resolve eq21819 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21819
  have eq21880 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (σ (τ (M.op (k X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq21854 X0
       have i₂ := eq16295 X0
       grind)
    | exact superpose eq16295 eq21854
    | exact resolve eq21854 eq16295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21854
  have eq21900 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq21880 X0
       have i₂ := eq11 (M.op (k X0 X0) X0)
       grind)
    | exact superpose eq11 eq21880
    | exact resolve eq21880 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21880
  have eq34316 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (M.op (k X0 X0) X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq64 (σ X0) (σ X0)
       have i₂ := eq16372 X0
       grind)
    | exact superpose eq16372 eq64
    | (have j1 := eq16372 X0
       grind)
    | exact resolve eq64 eq16372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq34317 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ (M.op (k X0 X0) X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq69 (σ X0) (σ X0)
       have i₂ := eq16372 X0
       grind)
    | exact superpose eq16372 eq69
    | (have j1 := eq16372 X0
       grind)
    | exact resolve eq69 eq16372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq16372
  have eq35617 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (M.op (k (τ X0) (τ X0)) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34316 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq34316
    | exact resolve eq34316 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34316
  have eq35764 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (M.op (τ (k X0 X0)) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq35617 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq35617
    | (have j0 := eq35617 X0
       grind)
    | exact resolve eq35617 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35617
  have eq35791 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (τ (M.op (k X0 X0) X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq35764 X0
       have i₂ := eq16295 X0
       grind)
    | exact superpose eq16295 eq35764
    | (have j0 := eq35764 X0
       grind)
    | exact resolve eq35764 eq16295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35764
  have eq35811 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (k X0 X0) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq35791 X0
       have i₂ := eq11 (M.op (k X0 X0) X0)
       grind)
    | exact superpose eq11 eq35791
    | (have j0 := eq35791 X0
       grind)
    | exact resolve eq35791 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35791
  have eq36659 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq720
       have i₂ := eq4254 x y
       grind)
    | exact superpose eq4254 eq720
    | (have j1 := eq4254 (σ x) (σ y)
       grind)
    | (have r₁ := eq720
       have r₂ := eq4254 x y
       grind)
    | exact resolve eq720 eq4254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720 eq4254
  have eq36660 : y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq36659
  have eq39130 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ (M.op (k (τ X0) (τ X0)) (τ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34317 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq34317
    | exact resolve eq34317 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34317
  have eq39274 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ (M.op (τ (k X0 X0)) (τ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq39130 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq39130
    | (have j0 := eq39130 X0
       grind)
    | exact resolve eq39130 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq39130
  have eq39287 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ (τ (M.op (k X0 X0) X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq39274 X0
       have i₂ := eq16295 X0
       grind)
    | exact superpose eq16295 eq39274
    | (have j0 := eq39274 X0
       grind)
    | exact resolve eq39274 eq16295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16295 eq39274
  have eq39296 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq39287 X0
       have i₂ := eq11 (M.op (k X0 X0) X0)
       grind)
    | exact superpose eq11 eq39287
    | (have j0 := eq39287 X0
       grind)
    | exact resolve eq39287 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39287
  have eq39330 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq63 (k X0 X0) X0 X0
       have i₂ := eq39296 X0
       grind)
    | exact superpose eq39296 eq63
    | (have j1 := eq39296 X0
       grind)
    | exact resolve eq63 eq39296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq39296
  have eq39576 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) (k (σ X0) (σ X0)))) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39330 (σ x)
       have i₂ := eq468 x x
       grind)
    | exact superpose eq468 eq39330
    | (have j0 := eq39330 (σ X0)
       have j1 := eq468 X0 X0
       grind)
    | exact resolve eq39330 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468 eq39330
  have eq39673 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) (k (σ X0) (σ X0)))) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq39576 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39576
  have eq39684 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) (k (σ X0) (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq39673 X0
       have j1 := eq743 X0
       grind)
    | (have r₁ := eq39673 X0
       have r₂ := eq743 X0
       grind)
    | exact resolve eq39673 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743 eq39673
  have eq39688 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39684 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq39684
    | (have j0 := eq39684 X0
       grind)
    | exact resolve eq39684 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39684
  have eq44932 : ∀ X0 : G, (σ (τ X0)) = (M.op (k X0 (σ (τ X0))) (M.op (σ (τ X0)) (k X0 (σ (τ X0))))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq39688 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq39688
    | (have j0 := eq39688 (τ X0)
       grind)
    | exact resolve eq39688 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq39688
  have eq45051 : ∀ X0 : G, (M.op (k X0 X0) (M.op X0 (k X0 X0))) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq44932 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq44932
    | (have j0 := eq44932 X0
       grind)
    | exact resolve eq44932 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44932
  have eq45107 : ∀ X0 : G, (M.op (k X0 X0) (M.op X0 (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq45051 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq45051
    | (have j0 := eq45051 X0
       grind)
    | exact resolve eq45051 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45051
  have eq45207 : ∀ X0 : G, (k X0 X0) = (M.op (M.op (k X0 X0) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq76 (k X0 X0) (M.op X0 (k X0 X0))
       have i₂ := eq45107 X0
       grind)
    | exact superpose eq45107 eq76
    | (have j1 := eq45107 X0
       grind)
    | exact resolve eq76 eq45107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45107
  have eq46237 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq35811 X0
       have i₂ := eq45207 X0
       grind)
    | exact superpose eq45207 eq35811
    | (have j0 := eq35811 X0
       have j1 := eq45207 X0
       grind)
    | exact resolve eq35811 eq45207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35811 eq45207
  have eq46379 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq46237 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46237
  have eq46817 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq46379 (σ X0)
       grind)
    | exact superpose eq46379 eq15
    | (have j1 := eq46379 (σ X0)
       grind)
    | exact resolve eq15 eq46379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46379
  have eq49068 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  clear eq46817
  have eq49133 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq49068 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq49068
    | (have j0 := eq49068 X0
       grind)
    | exact resolve eq49068 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49068
  have eq49134 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq49133 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49133
  have eq49211 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq49134 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq49134
    | exact resolve eq49134 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49525 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq49211 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq49211
    | exact resolve eq49211 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq49211
  have eq49604 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq49525 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq49525
    | exact resolve eq49525 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49525
  have eq49853 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq21900 X0
       have i₂ := eq49604 X0
       grind)
    | exact superpose eq49604 eq21900
    | exact resolve eq21900 eq49604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21900
  have eq679754 : x = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq89 x y
       have i₂ := eq36660
       grind)
    | exact superpose eq36660 eq89
    | exact resolve eq89 eq36660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq679891 : (σ x) = (σ (k y y)) ∨ x = (M.op y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq679754
       have i₂ := eq49134 y
       grind)
    | exact superpose eq49134 eq679754
    | exact resolve eq679754 eq49134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679754
  have eq679980 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq679891
       have i₂ := eq49604 y
       grind)
    | exact superpose eq49604 eq679891
    | exact resolve eq679891 eq49604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679891
  have eq1496612 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq679980
       have i₂ := eq36660
       grind)
    | exact superpose eq36660 eq679980
    | exact resolve eq679980 eq36660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36660 eq679980
  have eq1496765 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1496612
  have eq1496807 : (σ x) = (σ (k y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1496765
       have i₂ := eq49134 y
       grind)
    | exact superpose eq49134 eq1496765
    | exact resolve eq1496765 eq49134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1496765
  have eq1496808 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1496807
       have i₂ := eq49604 y
       grind)
    | exact superpose eq49604 eq1496807
    | exact resolve eq1496807 eq49604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1496807
  have eq1496809 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1496808
  have eq1496903 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq76 (σ x) (σ y)
       have i₂ := eq1496809
       grind)
    | exact superpose eq1496809 eq76
    | exact resolve eq76 eq1496809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq1507707 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1496903
       have i₂ := eq1496809
       grind)
    | exact superpose eq1496809 eq1496903
    | exact resolve eq1496903 eq1496809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1496809 eq1496903
  have eq1507895 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1507707
  have eq1507948 : (σ x) = (σ (k y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1507895
       have i₂ := eq49134 y
       grind)
    | exact superpose eq49134 eq1507895
    | exact resolve eq1507895 eq49134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49134 eq1507895
  have eq1507979 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1507948
       have i₂ := eq49604 y
       grind)
    | exact superpose eq49604 eq1507948
    | exact resolve eq1507948 eq49604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49604 eq1507948
  have eq1507980 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq1507979
  have eq1508142 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1507980
       grind)
    | exact superpose eq1507980 eq10
    | exact resolve eq10 eq1507980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1507980
  have eq1508744 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1508142
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1508142
    | exact resolve eq1508142 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1508142
  have eq1508745 : x = (M.op y y) := by grind
  clear eq1508744
  have eq1509102 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq49853 y
       have i₂ := eq1508745
       grind)
    | exact superpose eq1508745 eq49853
    | exact resolve eq49853 eq1508745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49853 eq1508745
  have eq1509672 : False := by grind
  exact eq1509672

/-- `Equation1446`: `x = (x ◇ y) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pxy_pyx_pxy_Equation1446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17
    | exact resolve eq17 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq23 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq45 : ∀ X1 X2 X3 : G, (M.op (M.op X3 (M.op X1 X2)) (M.op X3 X1)) = X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X1 X2) (M.op X1 (M.op X2 x))
       have i₂ := eq9 X1 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op X1 X2) X1) X1) := by
    intro X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X2) X1 (M.op X2 x)
       have i₂ := eq9 X1 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op X1 X2) X1)) := by
    intro X1 X2
    first
    | (have i₁ := eq45 X1 (M.op X2 x) (M.op X1 X2)
       have i₂ := eq9 X1 X2 x
       grind)
    | exact superpose eq9 eq45
    | exact resolve eq45 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X1 X2 : G, (M.op (M.op X1 (M.op X1 X2)) (M.op X1 X2)) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq46 (M.op x X1) (M.op x (M.op X1 X2))
       have i₂ := eq9 x X1 X2
       grind)
    | exact superpose eq9 eq46
    | exact resolve eq46 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (M.op X1 X2))) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq49 (M.op x X1) (M.op x (M.op X1 X2))
       have i₂ := eq9 x X1 X2
       grind)
    | exact superpose eq9 eq49
    | exact resolve eq49 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq106 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq106 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq106 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq108 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0 X0
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq23
    | exact resolve eq23 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq109 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq15
    | exact resolve eq15 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq109 X0
       have i₂ := eq107 (σ X0)
       grind)
    | exact superpose eq107 eq109
    | exact resolve eq109 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq111 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq108 X0
       have i₂ := eq107 (τ X0)
       grind)
    | exact superpose eq107 eq108
    | exact resolve eq108 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq108
  have eq112 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq10
    | exact resolve eq10 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq359 X0 X1
       grind)
    | exact superpose eq359 eq15
    | (have j1 := eq359 X0 X1
       grind)
    | exact resolve eq15 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq361 x y
       grind)
    | exact superpose eq361 eq16
    | (have j1 := eq361 x y
       grind)
    | exact resolve eq16 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq393 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq374
       have i₂ := eq359 (σ x) (σ y)
       grind)
    | exact superpose eq359 eq374
    | (have j1 := eq359 x y
       grind)
    | (have r₁ := eq374
       have r₂ := eq359 (σ x) (σ y)
       grind)
    | exact resolve eq374 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359 eq374
  have eq394 : (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq393
  have eq412 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq110 y
       have i₂ := eq394
       grind)
    | exact superpose eq394 eq110
    | exact resolve eq110 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq416 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq412
       have i₂ := eq110 x
       grind)
    | exact superpose eq110 eq412
    | exact resolve eq412 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq417 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq416
  have eq435 : (τ (M.op (σ x) (σ x))) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq111 (σ y)
       have i₂ := eq417
       grind)
    | exact superpose eq417 eq111
    | exact resolve eq111 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq13 (σ y) X0
       have i₂ := eq417
       grind)
    | exact superpose eq417 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq417
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq417
       grind)
    | exact resolve eq13 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq441 : (M.op y y) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq435
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq435
    | exact resolve eq435 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq442 : (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq441
       have i₂ := eq112 x
       grind)
    | exact superpose eq112 eq441
    | exact resolve eq441 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq441
  have eq444 : ∀ X0 : G, (M.op (M.op X0 y) (M.op X0 (M.op x x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq442
       grind)
    | exact superpose eq442 eq9
    | exact resolve eq9 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq449 : (M.op x x) = (M.op (M.op (M.op x x) y) y) := by
    first
    | (have i₁ := eq46 y y
       have i₂ := eq442
       grind)
    | exact superpose eq442 eq46
    | exact resolve eq46 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq450 : (M.op x x) = (M.op y (M.op (M.op x x) y)) := by
    first
    | (have i₁ := eq49 y y
       have i₂ := eq442
       grind)
    | exact superpose eq442 eq49
    | exact resolve eq49 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq453 : y = (M.op (M.op y (M.op x x)) (M.op x x)) := by
    first
    | (have i₁ := eq56 y y
       have i₂ := eq442
       grind)
    | exact superpose eq442 eq56
    | exact resolve eq56 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq454 : y = (M.op (M.op x x) (M.op y (M.op x x))) := by
    first
    | (have i₁ := eq65 y y
       have i₂ := eq442
       grind)
    | exact superpose eq442 eq65
    | exact resolve eq65 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq461 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq442
       grind)
    | exact superpose eq442 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq442
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq442
       grind)
    | exact resolve eq13 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq498 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op (M.op (M.op x (M.op x X0)) y) x) := by
    intro X0
    first
    | (have i₁ := eq444 (M.op x (M.op x X0))
       have i₂ := eq45 x X0 x
       grind)
    | exact superpose eq45 eq444
    | exact resolve eq444 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq444
  have eq3450 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have j0 := eq461 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq3456 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq15 y x
       have i₂ := eq3450
       grind)
    | exact superpose eq3450 eq15
    | exact resolve eq15 eq3450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3450
  have eq3464 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3456
       grind)
    | exact superpose eq3456 eq16
    | exact resolve eq16 eq3456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3456
  have eq13984 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j0 := eq437 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq13988 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3464
       have i₂ := eq13984
       grind)
    | exact superpose eq13984 eq3464
    | (have r₁ := eq3464
       have r₂ := eq13984
       grind)
    | exact resolve eq3464 eq13984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3464 eq13984
  have eq13992 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq13988
  have eq14013 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq111 (σ x)
       have i₂ := eq13992
       grind)
    | exact superpose eq13992 eq111
    | exact resolve eq111 eq13992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq13992
  have eq14073 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14013
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq14013
    | exact resolve eq14013 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14013
  have eq14074 : x = (M.op x x) := by grind
  clear eq14073
  have eq14081 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq449
       have i₂ := eq14074
       grind)
    | exact superpose eq14074 eq449
    | exact resolve eq449 eq14074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq14082 : x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq450
       have i₂ := eq14074
       grind)
    | exact superpose eq14074 eq450
    | exact resolve eq450 eq14074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq14085 : y = (M.op (M.op y x) x) := by
    first
    | (have i₁ := eq453
       have i₂ := eq14074
       grind)
    | exact superpose eq14074 eq453
    | exact resolve eq453 eq14074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq14086 : y = (M.op x (M.op y x)) := by
    first
    | (have i₁ := eq454
       have i₂ := eq14074
       grind)
    | exact superpose eq14074 eq454
    | exact resolve eq454 eq14074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq14429 : (M.op x y) = (M.op (M.op (M.op x y) y) x) := by
    first
    | (have i₁ := eq498 (M.op y x)
       have i₂ := eq14086
       grind)
    | exact superpose eq14086 eq498
    | exact resolve eq498 eq14086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498 eq14086
  have eq14505 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq14429
       have i₂ := eq14081
       grind)
    | exact superpose eq14081 eq14429
    | exact resolve eq14429 eq14081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14081 eq14429
  have eq14511 : x = (M.op x y) := by
    first
    | (have i₁ := eq14505
       have i₂ := eq14074
       grind)
    | exact superpose eq14074 eq14505
    | exact resolve eq14505 eq14074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14505
  have eq14513 : x = (M.op y x) := by
    first
    | (have i₁ := eq14082
       have i₂ := eq14511
       grind)
    | exact superpose eq14511 eq14082
    | exact resolve eq14082 eq14511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14082 eq14511
  have eq14611 : y = (M.op x x) := by
    first
    | (have i₁ := eq14085
       have i₂ := eq14513
       grind)
    | exact superpose eq14513 eq14085
    | exact resolve eq14085 eq14513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14085 eq14513
  have eq14695 : x = y := by
    first
    | (have i₁ := eq14611
       have i₂ := eq14074
       grind)
    | exact superpose eq14074 eq14611
    | exact resolve eq14611 eq14074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14074 eq14611
  have eq14703 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14695
       grind)
    | exact superpose eq14695 eq16
    | exact resolve eq16 eq14695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14695
  have eq14787 : False := by grind
  exact eq14787

/-- `Equation1446`: `x = (x ◇ y) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxy_y_pxy_Equation1446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq62 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X0 X2) (M.op X0 (M.op X2 x))
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 (M.op X0 X1) (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq62 (M.op X0 X1) X0 X0
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq62
    | exact resolve eq62 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq455 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq456 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq455 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq459 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq456 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq456 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq456 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq472 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq459 (σ X0)
       grind)
    | exact superpose eq459 eq15
    | exact resolve eq15 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq472 X0
       have i₂ := eq459 X0
       grind)
    | exact superpose eq459 eq472
    | exact resolve eq472 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459 eq472
  have eq536 : ∀ X0 X1 : G, (M.op (M.op X1 (σ (M.op X0 X0))) (M.op X1 (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq62 (σ X0) X1 (σ X0)
       have i₂ := eq491 X0
       grind)
    | exact superpose eq491 eq62
    | exact resolve eq62 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq537 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) (M.op (σ X0) X1)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (σ X0) (σ X0) X1
       have i₂ := eq491 X0
       grind)
    | exact superpose eq491 eq62
    | exact resolve eq62 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq491 X0
       grind)
    | exact superpose eq491 eq14
    | (have j0 := eq14 X1 X1
       grind)
    | exact resolve eq14 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq491 X0
       grind)
    | exact superpose eq491 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq549 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq546 X0 X1
       have j1 := eq548 X0 X1
       grind)
    | (have r₁ := eq546 X0 X1
       have r₂ := eq548 X0 X1
       grind)
    | exact resolve eq546 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546 eq548
  have eq813 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq549 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq549
    | (have j0 := eq549 X0 X1
       grind)
    | exact resolve eq549 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq824 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq549 X1 (σ X0)
       grind)
    | exact superpose eq549 eq15
    | (have j1 := eq549 X0 (σ X0)
       grind)
    | exact resolve eq15 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq843 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq824 X0 X1
       have i₂ := eq491 X0
       grind)
    | exact superpose eq491 eq824
    | (have j0 := eq824 X0 X1
       grind)
    | exact resolve eq824 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq861 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq813 (τ X1) X0
       grind)
    | exact superpose eq813 eq18
    | (have j1 := eq813 X0 X0
       grind)
    | exact resolve eq18 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq813
  have eq1537 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq861 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq861
    | (have j0 := eq861 X1 X1
       grind)
    | exact resolve eq861 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861
  have eq1612 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1537 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1537
    | (have j0 := eq1537 X0 X1
       grind)
    | exact resolve eq1537 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537
  have eq2156 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq843 X0 X1
       grind)
    | exact superpose eq843 eq10
    | (have j1 := eq843 X0 X1
       grind)
    | exact resolve eq10 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq2204 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2156 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2156
    | (have j0 := eq2156 X0 X1
       grind)
    | exact resolve eq2156 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2156
  have eq2259 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2204 x y
       grind)
    | exact superpose eq2204 eq16
    | (have j1 := eq2204 x x
       grind)
    | exact resolve eq16 eq2204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2204
  have eq2346 : x = (M.op x x) := by
    first
    | (have j1 := eq1612 x x
       grind)
    | (have r₁ := eq2259
       have r₂ := eq1612 y x
       grind)
    | exact resolve eq2259 eq1612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1612 eq2259
  have eq2376 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op X0 (σ x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq536 x X0
       have i₂ := eq2346
       grind)
    | exact superpose eq2346 eq536
    | exact resolve eq536 eq2346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq2377 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq537 x X0
       have i₂ := eq2346
       grind)
    | exact superpose eq2346 eq537
    | exact resolve eq537 eq2346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq2400 : ∀ X0 : G, (M.op (M.op X0 x) (M.op X0 x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq62 x X0 x
       have i₂ := eq2346
       grind)
    | exact superpose eq2346 eq62
    | exact resolve eq62 eq2346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2401 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq62 x x X0
       have i₂ := eq2346
       grind)
    | exact superpose eq2346 eq62
    | exact resolve eq62 eq2346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq2594 : ∀ X0 : G, (M.op x x) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq2400 (M.op x (M.op x X0))
       have i₂ := eq2401 X0
       grind)
    | exact superpose eq2401 eq2400
    | exact resolve eq2400 eq2401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2401
  have eq2613 : ∀ X0 : G, x = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq2594 X0
       have i₂ := eq2346
       grind)
    | exact superpose eq2346 eq2594
    | exact resolve eq2594 eq2346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2594
  have eq2639 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq86 x X0
       have i₂ := eq2613 X0
       grind)
    | exact superpose eq2613 eq86
    | exact resolve eq86 eq2613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2613
  have eq2681 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq2400 (M.op x X0)
       have i₂ := eq2639 X0
       grind)
    | exact superpose eq2639 eq2400
    | exact resolve eq2400 eq2639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2400 eq2639
  have eq2700 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq2681 X0
       have i₂ := eq2346
       grind)
    | exact superpose eq2346 eq2681
    | exact resolve eq2681 eq2346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2681
  have eq4034 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq2376 (M.op (σ x) (M.op (σ x) X0))
       have i₂ := eq2377 X0
       grind)
    | exact superpose eq2377 eq2376
    | exact resolve eq2376 eq2377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2377
  have eq4061 : ∀ X0 : G, (σ (M.op x x)) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq4034 X0
       have i₂ := eq491 x
       grind)
    | exact superpose eq491 eq4034
    | exact resolve eq4034 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4034
  have eq4074 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq4061 X0
       have i₂ := eq2346
       grind)
    | exact superpose eq2346 eq4061
    | exact resolve eq4061 eq2346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4061
  have eq4116 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq86 (σ x) X0
       have i₂ := eq4074 X0
       grind)
    | exact superpose eq4074 eq86
    | exact resolve eq86 eq4074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq4074
  have eq4181 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq2376 (M.op (σ x) X0)
       have i₂ := eq4116 X0
       grind)
    | exact superpose eq4116 eq2376
    | exact resolve eq2376 eq4116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2376 eq4116
  have eq4208 : ∀ X0 : G, (σ (M.op x x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq4181 X0
       have i₂ := eq491 x
       grind)
    | exact superpose eq491 eq4181
    | exact resolve eq4181 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491 eq4181
  have eq4221 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq4208 X0
       have i₂ := eq2346
       grind)
    | exact superpose eq2346 eq4208
    | exact resolve eq4208 eq2346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2346 eq4208
  have eq4244 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4221 (σ y)
       grind)
    | exact superpose eq4221 eq16
    | exact resolve eq16 eq4221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4221
  have eq4357 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq4244
       have i₂ := eq2700 y
       grind)
    | exact superpose eq2700 eq4244
    | exact resolve eq4244 eq2700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2700 eq4244
  have eq4358 : False := by grind
  exact eq4358

/-- `Equation1446`: `x = (x ◇ y) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyy_pxy_Equation1446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq22 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq22 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq27 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq41 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq37 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq40 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       have j1 := eq41 X1 X0
       grind)
    | (have r₁ := eq47 X1 X0
       have r₂ := eq41 X0 X1
       grind)
    | exact resolve eq47 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq47
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq54
    | (have j0 := eq54 X0 X1
       grind)
    | exact resolve eq54 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq54
  have eq146 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq150 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq146 X0 X1
       have j1 := eq56 X0 X1
       grind)
    | (have r₁ := eq146 X0 X1
       have r₂ := eq56 X0 X1
       grind)
    | (have r₁ := eq146 X0 X0
       have r₂ := eq56 X0 X0
       grind)
    | exact resolve eq146 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq146
  have eq334 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq150 (σ X0) (σ X1)
       grind)
    | exact superpose eq150 eq15
    | exact resolve eq15 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq341 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq334 X0 X1
       have i₂ := eq150 X0 X1
       grind)
    | exact superpose eq150 eq334
    | exact resolve eq334 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq334
  have eq344 : False := by grind
  exact eq344

/-- `Equation1446`: `x = (x ◇ y) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_x_pyx_Equation1446 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1446 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1446.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X2))) = X0 := by
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) X0))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 (M.op X0 X2) (M.op X0 (M.op X2 x))
       have i₂ := eq16 X0 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 X1) X0 (M.op X1 x)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : x = (M.op (M.op x y) (M.op x (k y y))) := by
    first
    | (have i₁ := eq175 y
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq175
    | exact resolve eq175 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op X0 x)) = X0 := by
    intro X0
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq191 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (k (σ y) (σ y)))) := by
    first
    | (have i₁ := eq176 sF3
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq176
    | exact resolve eq176 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq213 : x = (M.op (M.op x (M.op x y)) (k x x)) := by
    first
    | (have i₁ := eq187 x
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq187
    | exact resolve eq187 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq222 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq193 sF2
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq193
    | exact resolve eq193 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq542 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ x = y := by
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
  have eq553 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
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
  have eq571 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq553
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq553
    | exact resolve eq553 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq582 : (M.op x y) = (k y x) ∨ x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq542
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq542
    | exact resolve eq542 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq775 : (M.op x y) = (M.op x (M.op (M.op x y) x)) := by
    first
    | exact superpose eq185 eq180
    | exact resolve eq180 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq777 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq191 eq180
    | exact resolve eq180 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq814 : x = (M.op (M.op x y) (M.op x (M.op x y))) := by
    first
    | exact superpose eq775 eq180
    | exact resolve eq180 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq826 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq777 eq180
    | exact resolve eq180 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1587 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq582
       grind)
    | exact superpose eq582 eq39
    | exact resolve eq39 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq1588 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq1587
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1587
    | exact resolve eq1587 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1587
  have eq1590 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq20 eq1588
    | exact resolve eq1588 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1588
  have eq3416 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq1590 eq571
    | exact resolve eq571 eq1590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571 eq1590
  have eq3425 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq3416
       have r₂ := eq27
       grind)
    | exact resolve eq3416 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3416
  have eq3437 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq3425 eq141
    | exact resolve eq141 eq3425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq3425
  have eq3454 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq29 eq3437
    | exact resolve eq3437 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3437
  have eq3455 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3454
  have eq3469 : x = (M.op (M.op x (M.op x y)) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq213
       have i₂ := eq3455
       grind)
    | exact superpose eq3455 eq213
    | exact resolve eq213 eq3455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq3475 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq3455
       grind)
    | exact superpose eq3455 eq39
    | exact resolve eq39 eq3455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3492 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3475
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3475
    | exact resolve eq3475 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3475
  have eq3514 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3492 eq222
    | exact resolve eq222 eq3492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq3627 : (M.op x x) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3469 eq181
    | exact resolve eq181 eq3469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3469
  have eq3656 : (k x x) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3627
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq3627
    | exact resolve eq3627 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3627
  have eq3666 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3455 eq3656
    | exact resolve eq3656 eq3455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3455 eq3656
  have eq3677 : x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3666 eq814
    | exact resolve eq814 eq3666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814 eq3666
  have eq3756 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3677 eq775
    | exact resolve eq775 eq3677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775 eq3677
  have eq3788 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3756
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq3756
    | exact resolve eq3756 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3756
  have eq3800 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq3788
       grind)
    | exact superpose eq3788 eq39
    | exact resolve eq39 eq3788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3788
  have eq3812 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3800
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3800
    | exact resolve eq3800 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3800
  have eq3814 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq3812
    | exact resolve eq3812 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3812
  have eq3816 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq3492 eq3814
    | exact resolve eq3814 eq3492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3814
  have eq5035 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3514 eq181
    | exact resolve eq181 eq3514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq3514
  have eq5068 : (k (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5035
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq5035
    | exact resolve eq5035 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5035
  have eq5078 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3492 eq5068
    | exact resolve eq5068 eq3492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5068
  have eq5089 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq5078 eq826
    | exact resolve eq826 eq5078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826 eq5078
  have eq5171 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq5089 eq777
    | exact resolve eq777 eq5089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777 eq5089
  have eq5207 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5171
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq5171
    | exact resolve eq5171 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5171
  have eq5210 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3492 eq5207
    | exact resolve eq5207 eq3492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3492 eq5207
  have eq5212 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq5210 eq27
    | exact resolve eq27 eq5210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5210
  have eq5268 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq5212
       have r₂ := eq3816
       grind)
    | exact resolve eq5212 eq3816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3816 eq5212
  have eq5284 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq5268 eq31
    | exact resolve eq31 eq5268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq5268
  have eq5312 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq5284
    | exact resolve eq5284 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq5284
  have eq5313 : x = y := by grind
  clear eq5312
  have eq5325 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq5313
       grind)
    | exact superpose eq5313 eq18
    | exact resolve eq18 eq5313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq5326 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq5313
       grind)
    | exact superpose eq5313 eq24
    | exact resolve eq24 eq5313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq5313
  have eq5337 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq5326
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5326
    | exact resolve eq5326 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5326
  have eq5338 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq5325
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq5325
    | exact resolve eq5325 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5325
  have eq5339 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5337 eq26
    | exact resolve eq26 eq5337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq5337
  have eq5367 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq5339
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq5339
    | exact resolve eq5339 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq5339
  have eq5378 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq5338
       grind)
    | exact superpose eq5338 eq39
    | exact resolve eq39 eq5338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq5338
  have eq5388 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq5378
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5378
    | exact resolve eq5378 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5378
  have eq5390 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5367 eq5388
    | exact resolve eq5388 eq5367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5367 eq5388
  have eq5392 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq5390
    | exact resolve eq5390 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5390
  have eq5394 : False := by grind
  exact eq5394

/-- `Equation1460`: `x = (x ◇ y) ◇ (y ◇ (z ◇ w))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_pxx_pxy_pyx_Equation1460 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1460 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1460.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X2 X3))) = X0 := by
    intro X0 X1 X2 X3
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq51 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op y (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x y X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0 X1
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 (M.op x y))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op X0 x) (M.op x (M.op x x))
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X0 X2) X2 (M.op x x)
       have i₂ := eq14 X0 X2 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : y ≠ (M.op x y) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq77 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq80 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq81 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq37 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq85 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq92 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq85
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq76
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq76 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq93
    | exact resolve eq93 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq99
    | exact resolve eq99 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq100
    | exact resolve eq100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq77
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq77
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq77 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq102
  have eq211 : ∀ X0 : G, x = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 x) (M.op x (M.op x x))
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq338 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k X1 (M.op X0 (M.op X1 X2))) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 (M.op X0 (M.op X1 X2))
       have i₂ := eq57 X1 X0 X2
       grind)
    | exact superpose eq57 eq13
    | (have j0 := eq13 X1 (M.op X0 (M.op X1 X2))
       grind)
    | (have r₁ := eq13 X1 (M.op X1 (M.op X1 X2))
       have r₂ := eq57 X1 X1 X2
       grind)
    | exact resolve eq13 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op X0 (M.op X1 X2)) X1
       have i₂ := eq57 X1 X0 X2
       grind)
    | exact superpose eq57 eq54
    | exact resolve eq54 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq345 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X2 (M.op X0 (M.op X1 X3)) X1
       have i₂ := eq57 X1 X0 X3
       grind)
    | exact superpose eq57 eq56
    | exact resolve eq56 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq390 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    grind
  clear eq35
  have eq413 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 X1
       have i₂ := eq11 X1 (τ X0)
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 X1 (τ X0)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq542 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X2 (σ X1) (σ X0)
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq56
    | (have j1 := eq79 X0 X1
       grind)
    | exact resolve eq56 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq79 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq2601 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq338 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq2634 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op (M.op x y) x)) := by
    first
    | exact superpose eq51 eq2601
    | exact resolve eq2601 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq6543 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq80 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq80
    | (have j0 := eq80 x
       grind)
    | exact resolve eq80 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq6568 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6543
  have eq6576 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6568
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq6568
    | exact resolve eq6568 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6568
  have eq6590 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq6576
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq6576 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6576
  have eq6594 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq6590 eq50
    | exact resolve eq50 eq6590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq6734 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq81 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq81
    | (have j0 := eq81 y
       grind)
    | exact resolve eq81 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq6757 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6734
  have eq6762 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6757
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq6757
    | exact resolve eq6757 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6757
  have eq6783 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq6762
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq6762 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6762
  have eq6801 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq6783 eq107
    | exact resolve eq107 eq6783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq7331 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq413 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq413
    | exact resolve eq413 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq7504 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7331 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq7331
    | (have j0 := eq7331 X0 X1
       grind)
    | exact resolve eq7331 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7331
  have eq8493 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq6590 eq92
    | exact resolve eq92 eq6590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq8734 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8735 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq8734
    | exact resolve eq8734 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8734
  have eq8746 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq8735
       have r₂ := eq28
       grind)
    | exact resolve eq8735 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8735
  have eq8748 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq8746
    | exact resolve eq8746 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8746
  have eq8750 : (τ (σ x)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq8748 eq6801
    | exact resolve eq6801 eq8748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8748
  have eq8799 : x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq8750
    | exact resolve eq8750 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8750
  have eq8869 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq8799
       grind)
    | exact superpose eq8799 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq8799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8870 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq8869
  have eq9678 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq8870
       grind)
    | exact superpose eq8870 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq8870
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq8870
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq8870
       grind)
    | exact resolve eq13 eq8870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9697 : x ≠ y ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq8870
  have eq9698 : y = (k y y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq9678
  have eq10287 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8799
       have i₂ := eq9698
       grind)
    | exact superpose eq9698 eq8799
    | exact resolve eq8799 eq9698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8799 eq9698
  have eq10300 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq10287
  have eq10306 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10300
       have r₂ := eq9697
       grind)
    | exact resolve eq10300 eq9697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9697 eq10300
  have eq10329 : (M.op x y) = (k x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq303 y
       have i₂ := eq10306
       grind)
    | exact superpose eq10306 eq303
    | exact resolve eq303 eq10306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq10340 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq56 X0 y y
       have i₂ := eq10306
       grind)
    | exact superpose eq10306 eq56
    | exact resolve eq56 eq10306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10342 : ∀ X0 : G, (M.op (M.op X0 x) y) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq57 y X0 y
       have i₂ := eq10306
       grind)
    | exact superpose eq10306 eq57
    | exact resolve eq57 eq10306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10347 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq345 X0 y y X1
       have i₂ := eq10306
       grind)
    | exact superpose eq10306 eq345
    | exact resolve eq345 eq10306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq10356 : (M.op x y) = (k x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10329
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10329
    | exact resolve eq10329 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10329
  have eq10691 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10340 y
       have i₂ := eq10306
       grind)
    | exact superpose eq10306 eq10340
    | exact resolve eq10340 eq10306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10306 eq10340
  have eq10748 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10691
  have eq10766 : x ≠ y ∨ y = (k x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq10748
       grind)
    | exact superpose eq10748 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq10748
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq10748
       grind)
    | exact resolve eq13 eq10748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13935 : ∀ X0 : G, (σ x) = (M.op (k (σ y) (σ x)) (M.op (σ y) X0)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq542 y x X0
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq542
    | (have j0 := eq542 y x x
       grind)
    | exact resolve eq542 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq14148 : ∀ X0 : G, (σ x) = (M.op (k (σ y) (σ x)) (M.op (σ y) X0)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13935 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13935
    | (have j0 := eq13935 X0
       grind)
    | exact resolve eq13935 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13935
  have eq14264 : ∀ X0 : G, (σ x) = (M.op (k (σ y) (σ x)) (M.op (σ y) X0)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14148 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14148
    | (have j0 := eq14148 X0
       grind)
    | exact resolve eq14148 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14148
  have eq14377 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (k (σ y) (σ x)) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14264 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14264
    | (have j0 := eq14264 X0
       grind)
    | exact resolve eq14264 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14264
  have eq14472 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (k (σ y) (σ x)) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14377 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14377
    | (have j0 := eq14377 X0
       grind)
    | exact resolve eq14377 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14377
  have eq14560 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (k (σ y) (σ x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq14472 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14472
    | (have j0 := eq14472 X0
       grind)
    | exact resolve eq14472 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14472
  have eq14646 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (k (σ y) (σ x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq14560 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14560
    | (have j0 := eq14560 X0
       grind)
    | exact resolve eq14560 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14560
  have eq14717 : ∀ X0 : G, (σ x) = (M.op (k (σ y) (σ x)) (M.op (σ y) X0)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14646
    | (have j0 := eq14646 X0
       grind)
    | exact resolve eq14646 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14646
  have eq14805 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (τ X0) (M.op (τ X0) (M.op x y)))) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq390 X0
       have i₂ := eq343 (τ X0) (τ X0) (τ X0)
       grind)
    | exact superpose eq343 eq390
    | (have j0 := eq390 X0
       grind)
    | exact resolve eq390 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq390
  have eq14938 : ∀ X0 : G, (k X0 (τ (σ (M.op (τ (σ X0)) (τ (σ X0)))))) = (τ (σ (M.op (τ (σ X0)) (M.op (τ (σ X0)) (M.op x y))))) ∨ (τ (σ X0)) = (M.op (M.op (τ (σ X0)) (τ (σ X0))) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq418 X0 (σ (M.op (τ (σ X0)) (τ (σ X0))))
       have i₂ := eq14805 (σ X0)
       grind)
    | exact superpose eq14805 eq418
    | (have j1 := eq14805 (σ X0)
       grind)
    | exact resolve eq418 eq14805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418 eq14805
  have eq14941 : ∀ X0 : G, (M.op (τ (σ X0)) (M.op (τ (σ X0)) (M.op x y))) = (k X0 (τ (σ (M.op (τ (σ X0)) (τ (σ X0)))))) ∨ (τ (σ X0)) = (M.op (M.op (τ (σ X0)) (τ (σ X0))) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq14938 X0
       have i₂ := eq16 (M.op (τ (σ X0)) (M.op (τ (σ X0)) sF0))
       grind)
    | exact superpose eq16 eq14938
    | (have j0 := eq14938 X0
       grind)
    | exact resolve eq14938 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14938
  have eq14999 : ∀ X0 : G, (M.op (τ (σ X0)) (M.op (τ (σ X0)) (M.op x y))) = (k X0 (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (τ (σ X0)) = (M.op (M.op (τ (σ X0)) (τ (σ X0))) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq14941 X0
       have i₂ := eq16 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq16 eq14941
    | (have j0 := eq14941 X0
       grind)
    | exact resolve eq14941 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14941
  have eq15024 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 (M.op x y))) ∨ (τ (σ X0)) = (M.op (M.op (τ (σ X0)) (τ (σ X0))) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq14999 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq14999
    | (have j0 := eq14999 X0
       grind)
    | exact resolve eq14999 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14999
  have eq15031 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 (M.op x y))) ∨ (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15024 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq15024
    | (have j0 := eq15024 X0
       grind)
    | exact resolve eq15024 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15024
  have eq18001 : (M.op y y) = (k y (M.op y x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2601 y x
       have i₂ := eq10347 y x
       grind)
    | exact superpose eq10347 eq2601
    | exact resolve eq2601 eq10347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2601 eq10347
  have eq18135 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6783 eq108
    | exact resolve eq108 eq6783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq19558 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq10356
       grind)
    | exact superpose eq10356 eq45
    | exact resolve eq45 eq10356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq10356
  have eq19586 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq19558
    | exact resolve eq19558 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19558
  have eq29823 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8493
       have i₂ := eq10748
       grind)
    | exact superpose eq10748 eq8493
    | exact resolve eq8493 eq10748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8493 eq10748
  have eq29894 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29823
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq29823
    | exact resolve eq29823 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29823
  have eq29911 : (τ (σ y)) = (k x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29894 eq6594
    | exact resolve eq6594 eq29894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29894
  have eq29970 : y = (k x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq29911
    | exact resolve eq29911 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq29911
  have eq29971 : y = (k x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq29970
       have r₂ := eq10766
       grind)
    | exact resolve eq29970 eq10766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10766 eq29970
  have eq29973 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq29971
       grind)
    | exact superpose eq29971 eq44
    | exact resolve eq44 eq29971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq29971
  have eq30011 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6590 eq29973
    | exact resolve eq29973 eq6590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6590 eq29973
  have eq30026 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30011
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq30011
    | exact resolve eq30011 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30011
  have eq30055 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq30066 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ y)) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq30026 eq56
    | exact resolve eq56 eq30026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30026
  have eq30095 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq30055
    | exact resolve eq30055 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30055
  have eq40001 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30095 eq19586
    | exact resolve eq19586 eq30095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19586 eq30095
  have eq40010 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq40001
  have eq40014 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq40010
       have r₂ := eq28
       grind)
    | exact resolve eq40010 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40010
  have eq40025 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq40014 eq30066
    | exact resolve eq30066 eq40014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30066 eq40014
  have eq40058 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq40025
  have eq40072 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq40058
    | exact resolve eq40058 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40058
  have eq40073 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq40072
  have eq40087 : (k y x) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18001
       have i₂ := eq40073
       grind)
    | exact superpose eq40073 eq18001
    | exact resolve eq18001 eq40073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18001
  have eq40094 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10342 y
       have i₂ := eq40073
       grind)
    | exact superpose eq40073 eq10342
    | exact resolve eq10342 eq40073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10342 eq40073
  have eq40126 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq40094
  have eq40129 : (k y x) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq40087
  have eq40142 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40126
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq40126
    | exact resolve eq40126 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40126
  have eq40143 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq40142
  have eq40148 : (k y x) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq40129
       have r₂ := eq67
       grind)
    | exact resolve eq40129 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40129
  have eq40153 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40143 eq68
    | (have r₁ := eq68
       have r₂ := eq40143
       grind)
    | exact resolve eq68 eq40143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40143
  have eq40170 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq40153
  have eq40180 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq40148
       grind)
    | exact superpose eq40148 eq76
    | exact resolve eq76 eq40148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40195 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq546 x y
       have i₂ := eq40148
       grind)
    | exact superpose eq40148 eq546
    | (have j0 := eq546 x y
       grind)
    | exact resolve eq546 eq40148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546 eq40148
  have eq40200 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40195
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq40195
    | exact resolve eq40195 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40195
  have eq40208 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40200
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq40200
    | exact resolve eq40200 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40200
  have eq40216 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40208
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq40208
    | exact resolve eq40208 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40208
  have eq40222 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40216
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq40216
    | exact resolve eq40216 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40216
  have eq40227 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40222
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq40222
    | exact resolve eq40222 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40222
  have eq40232 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq40227
    | exact resolve eq40227 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40227
  have eq40233 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq40232
  have eq40699 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40170 eq98
    | exact resolve eq98 eq40170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40700 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40170 eq101
    | exact resolve eq101 eq40170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq40170
  have eq40719 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq40700
  have eq40729 : (k y x) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6801 eq40699
    | exact resolve eq40699 eq6801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40699
  have eq40907 : (k y x) = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq40729
       grind)
    | exact superpose eq40729 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq40729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40729
  have eq40919 : (k y x) = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq40907
  have eq40939 : (k y x) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq40919
       have r₂ := eq67
       grind)
    | exact resolve eq40919 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq40919
  have eq41517 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18135
       have i₂ := eq40180
       grind)
    | exact superpose eq40180 eq18135
    | exact resolve eq18135 eq40180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18135
  have eq41599 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq41517
       have r₂ := eq68
       grind)
    | exact resolve eq41517 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq41517
  have eq42433 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) X0)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq41599 eq14717
    | exact resolve eq14717 eq41599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14717 eq41599
  have eq42444 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq42433 x
       have i₂ := eq56 x sF3 sF3
       grind)
    | exact superpose eq56 eq42433
    | exact resolve eq42433 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42433
  have eq42695 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq40939
       grind)
    | exact superpose eq40939 eq76
    | exact resolve eq76 eq40939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq42705 : (M.op x y) = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq40939
       grind)
    | exact superpose eq40939 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq40939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40939
  have eq42718 : (M.op x y) = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq42705
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq42705
    | exact resolve eq42705 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42705
  have eq42726 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq42718
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq42718
    | exact resolve eq42718 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42718
  have eq58335 : (τ (σ (M.op x y))) = (k y y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq40719 eq6801
    | exact resolve eq6801 eq40719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40719
  have eq58431 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31 eq58335
    | exact resolve eq58335 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58335
  have eq105906 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq42444 eq6801
    | exact resolve eq6801 eq42444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42444
  have eq106002 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq29 eq105906
    | exact resolve eq105906 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105906
  have eq144022 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq40233
       have i₂ := eq106002
       grind)
    | exact superpose eq106002 eq40233
    | exact resolve eq40233 eq106002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40233
  have eq144037 : y ≠ y ∨ y = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq106002
       grind)
    | exact superpose eq106002 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq106002
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq106002
       grind)
    | exact resolve eq13 eq106002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106002
  have eq144067 : y = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by grind
  clear eq144037
  have eq144073 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k y y) := by grind
  clear eq144022
  have eq144108 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k y y) := by
    first
    | (have r₁ := eq144073
       have r₂ := eq25
       grind)
    | exact resolve eq144073 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144073
  have eq182652 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq144067
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq144067
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq144067 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144067
  have eq182742 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq182652
  have eq183739 : (τ (σ x)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k y y) := by
    first
    | exact superpose eq144108 eq6801
    | exact resolve eq6801 eq144108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6801 eq144108
  have eq183854 : x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k y y) := by
    first
    | exact superpose eq29 eq183739
    | exact resolve eq183739 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183739
  have eq183855 : x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq183854
  have eq183862 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq77
       have i₂ := eq183855
       grind)
    | exact superpose eq183855 eq77
    | exact resolve eq77 eq183855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq183953 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6783 eq183862
    | exact resolve eq183862 eq6783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6783 eq183862
  have eq183968 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq183953
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq183953
    | exact resolve eq183953 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183953
  have eq184034 : (k (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq183968 eq15031
    | exact resolve eq15031 eq183968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15031 eq183968
  have eq184084 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq184034
    | exact resolve eq184034 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184034
  have eq184085 : (k (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq184084
  have eq190720 : (σ y) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq184085 eq57
    | exact resolve eq57 eq184085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184085
  have eq256797 : y ≠ y ∨ y = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq182742
       grind)
    | exact superpose eq182742 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq182742
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq182742
       grind)
    | exact resolve eq13 eq182742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256831 : x ≠ y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq182742
  have eq256832 : y = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq256797
  have eq277214 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq183855
       have i₂ := eq256832
       grind)
    | exact superpose eq256832 eq183855
    | exact resolve eq183855 eq256832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183855 eq256832
  have eq277267 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq277214
  have eq277302 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq277267
       have r₂ := eq256831
       grind)
    | exact resolve eq277267 eq256831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256831 eq277267
  have eq277367 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40180
       have i₂ := eq277302
       grind)
    | exact superpose eq277302 eq40180
    | exact resolve eq40180 eq277302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40180 eq277302
  have eq277449 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq277367
  have eq277487 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq277449
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq277449
    | exact resolve eq277449 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277449
  have eq277679 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq277487 eq190720
    | exact resolve eq190720 eq277487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190720 eq277487
  have eq277703 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq277679
  have eq277722 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq277703
    | exact resolve eq277703 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277703
  have eq277723 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq277722
  have eq277739 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq277723 eq28
    | exact resolve eq28 eq277723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277723
  have eq1173222 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq56 X0 y y
       have i₂ := eq42726
       grind)
    | exact superpose eq42726 eq56
    | exact resolve eq56 eq42726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq42726
  have eq1173373 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq211 eq1173222
    | exact resolve eq1173222 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq1173222
  have eq1173532 : y ≠ y ∨ y = (k y y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq1173373
       grind)
    | exact superpose eq1173373 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq1173373
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1173373
       grind)
    | exact resolve eq13 eq1173373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173373
  have eq1173624 : y = (k y y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = y := by grind
  clear eq1173532
  have eq1175261 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq58431
       have i₂ := eq1173624
       grind)
    | exact superpose eq1173624 eq58431
    | exact resolve eq58431 eq1173624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58431 eq1173624
  have eq1175462 : x = (M.op y y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1175261
  have eq1175796 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq42695
       have i₂ := eq1175462
       grind)
    | exact superpose eq1175462 eq42695
    | exact resolve eq42695 eq1175462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42695
  have eq1175850 : (k y x) = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by grind
  have eq1175879 : ∀ X0 : G, (M.op (M.op X0 x) y) = X0 ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq57 y X0 y
       have i₂ := eq1175462
       grind)
    | exact superpose eq1175462 eq57
    | exact resolve eq57 eq1175462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq1175462
  have eq1175994 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq1175796
  have eq1176054 : y = (M.op x y) ∨ (k y x) = (M.op y x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1175850
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1175850
    | exact resolve eq1175850 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175850
  have eq1176055 : (k y x) = (M.op y x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1176054
  have eq1176069 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1175994
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1175994
    | exact resolve eq1175994 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175994
  have eq1176466 : (τ (σ x)) = (k y x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq1176069 eq98
    | exact resolve eq98 eq1176069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq1176069
  have eq1176819 : x = (k y x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq1176466
    | exact resolve eq1176466 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176466
  have eq1200303 : x = (M.op y x) ∨ x = y ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1176819
       have i₂ := eq1176055
       grind)
    | exact superpose eq1176055 eq1176819
    | exact resolve eq1176819 eq1176055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176055 eq1176819
  have eq1200364 : x = (M.op y x) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq1200303
  have eq1200560 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1175879 y
       have i₂ := eq1200364
       grind)
    | exact superpose eq1200364 eq1175879
    | exact resolve eq1175879 eq1200364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175879 eq1200364
  have eq1200661 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1200560
  have eq1200693 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1200661
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1200661
    | exact resolve eq1200661 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200661
  have eq1200694 : y = (M.op x y) ∨ x = y := by grind
  clear eq1200693
  have eq1200703 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1200694 eq21
    | exact resolve eq21 eq1200694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1201257 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1200703
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1200703
    | exact resolve eq1200703 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200703
  have eq1201907 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq1201257 eq277739
    | (have r₁ := eq277739
       have r₂ := eq1201257
       grind)
    | exact resolve eq277739 eq1201257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277739 eq1201257
  have eq1202345 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq1201907
  have eq1202571 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1202345 eq29
    | exact resolve eq29 eq1202345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1202345
  have eq1203636 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq1202571
    | exact resolve eq1202571 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1202571
  have eq1204236 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1203636 eq1200694
    | exact resolve eq1200694 eq1203636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200694 eq1203636
  have eq1204237 : x = y := by grind
  clear eq1204236
  have eq1204590 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1204237
       grind)
    | exact superpose eq1204237 eq19
    | exact resolve eq19 eq1204237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1204591 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1204237
       grind)
    | exact superpose eq1204237 eq25
    | exact resolve eq25 eq1204237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1204237
  have eq1205251 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1204591
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1204591
    | exact resolve eq1204591 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204591
  have eq1205289 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1205251 eq27
    | exact resolve eq27 eq1205251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1205251
  have eq1218882 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1205289 eq6594
    | exact resolve eq6594 eq1205289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6594 eq1205289
  have eq1241171 : (σ (M.op x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq7504 x x
       have i₂ := eq1218882
       grind)
    | exact superpose eq1218882 eq7504
    | (have j0 := eq7504 x x
       grind)
    | exact resolve eq7504 eq1218882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7504
  have eq1241207 : (σ (M.op x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x x) := by grind
  clear eq1241171
  have eq1241236 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1241207
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq1241207
    | exact resolve eq1241207 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241207
  have eq1241329 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1241236
       have i₂ := eq1204590
       grind)
    | exact superpose eq1204590 eq1241236
    | exact resolve eq1241236 eq1204590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241236
  have eq1241415 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq1241329
    | exact resolve eq1241329 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241329
  have eq1241478 : x = (M.op x x) := by
    first
    | (have r₁ := eq1241415
       have r₂ := eq28
       grind)
    | exact resolve eq1241415 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241415
  have eq1241526 : x = (M.op x y) := by
    first
    | (have i₁ := eq1241478
       have i₂ := eq1204590
       grind)
    | exact superpose eq1204590 eq1241478
    | exact resolve eq1241478 eq1204590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241478
  have eq1241601 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1241526 eq21
    | exact resolve eq21 eq1241526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq1241691 : (M.op x x) = (k x (M.op x x)) := by
    first
    | exact superpose eq1241526 eq2634
    | exact resolve eq2634 eq1241526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2634
  have eq1242291 : (M.op x y) = (k x (M.op x y)) := by
    first
    | (have i₁ := eq1241691
       have i₂ := eq1204590
       grind)
    | exact superpose eq1204590 eq1241691
    | exact resolve eq1241691 eq1204590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204590 eq1241691
  have eq1242361 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1241601
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1241601
    | exact resolve eq1241601 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241601
  have eq1242439 : x = (k x x) := by
    first
    | exact superpose eq1241526 eq1242291
    | exact resolve eq1242291 eq1241526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241526 eq1242291
  have eq1242550 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1242439
       have i₂ := eq1218882
       grind)
    | exact superpose eq1218882 eq1242439
    | exact resolve eq1242439 eq1218882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218882 eq1242439
  have eq1247093 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1242550 eq15
    | exact resolve eq15 eq1242550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242550
  have eq1247990 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1247093
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1247093
    | exact resolve eq1247093 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1247093
  have eq1248255 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1242361 eq1247990
    | exact resolve eq1247990 eq1242361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242361 eq1247990
  have eq1248485 : False := by grind
  exact eq1248485
