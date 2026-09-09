import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxx_pyx_pyx_pxx_pyx_Equation854 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq34 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    grind
  have eq81 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq91 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq20 X0 X0 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq99 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X0 X0)
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq9
    | exact resolve eq9 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq145 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq81 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq81 X0 X1
       grind)
    | exact superpose eq81 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq81 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq81 X1 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq81 X0 X1
       grind)
    | exact resolve eq13 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq166 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq145 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq167 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq166 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq169 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq167 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq167
    | (have j0 := eq167 X0 X1
       grind)
    | exact resolve eq167 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq172 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq169 X0 X1
       have j1 := eq163 X1 X0
       grind)
    | (have r₁ := eq169 X1 X0
       have r₂ := eq163 X0 X1
       grind)
    | (have r₁ := eq169 X1 (k X1 X0)
       have r₂ := eq163 X0 X1
       grind)
    | (have r₁ := eq169 X1 X1
       have r₂ := eq163 X1 X1
       grind)
    | exact resolve eq169 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq169
  have eq176 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq99 X0 (M.op X1 X0)
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq99
    | exact resolve eq99 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq469 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq176 (τ X0) (τ X0)
       grind)
    | exact superpose eq176 eq34
    | exact resolve eq34 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq825 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq172 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq172
    | exact resolve eq172 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq833 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq172 y x
       grind)
    | exact superpose eq172 eq16
    | (have j1 := eq172 y x
       grind)
    | exact resolve eq16 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq861 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq825 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq825
    | (have j0 := eq825 X0 X1
       grind)
    | exact resolve eq825 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq825
  have eq971 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq861 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq861
    | exact resolve eq861 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861
  have eq1116 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq971 (τ X0) X1
       grind)
    | exact superpose eq971 eq19
    | (have j1 := eq971 (τ X0) X1
       grind)
    | exact resolve eq19 eq971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq971
  have eq1397 : ∀ X0 : G, (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) = (k X0 (τ (σ (M.op (τ (σ X0)) (τ (σ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq31 X0 (σ (M.op (τ (σ X0)) (τ (σ X0))))
       have i₂ := eq469 (σ X0)
       grind)
    | exact superpose eq469 eq31
    | exact resolve eq31 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq1407 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ X0))) = (k X0 (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq1397 X0
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq1397
    | exact resolve eq1397 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397
  have eq1428 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1407 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1407
    | exact resolve eq1407 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407
  have eq1565 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq31 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq1428 (σ X0)
       grind)
    | exact superpose eq1428 eq31
    | exact resolve eq31 eq1428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq2115 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1116 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1116
    | exact resolve eq1116 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq2203 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2115 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2115
    | (have j0 := eq2115 X0 X1
       grind)
    | exact resolve eq2115 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2115
  have eq2388 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq833
       have i₂ := eq2203 x y
       grind)
    | exact superpose eq2203 eq833
    | (have j1 := eq2203 (σ x) (σ y)
       grind)
    | (have r₁ := eq833
       have r₂ := eq2203 x y
       grind)
    | exact resolve eq833 eq2203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2389 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq2388
  have eq2396 : (τ (σ x)) = (k y (τ (σ x))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1565 y
       have i₂ := eq2389
       grind)
    | exact superpose eq2389 eq1565
    | exact resolve eq1565 eq2389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1565
  have eq2426 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq176 (σ y) (σ y)
       have i₂ := eq2389
       grind)
    | exact superpose eq2389 eq176
    | exact resolve eq176 eq2389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2389
  have eq2445 : x = (k y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2396
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2396
    | exact resolve eq2396 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2396
  have eq2569 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2203 x y
       have i₂ := eq2445
       grind)
    | exact superpose eq2445 eq2203
    | (have j0 := eq2203 x y
       grind)
    | exact resolve eq2203 eq2445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2203 eq2445
  have eq2576 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by grind
  clear eq2569
  have eq2978 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2426
       grind)
    | exact superpose eq2426 eq16
    | exact resolve eq16 eq2426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2426
  have eq3016 : x = (M.op y y) := by
    first
    | (have r₁ := eq2978
       have r₂ := eq2576
       grind)
    | exact resolve eq2978 eq2576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2576 eq2978
  have eq3194 : x = (M.op x y) := by
    first
    | (have i₁ := eq176 y y
       have i₂ := eq3016
       grind)
    | exact superpose eq3016 eq176
    | exact resolve eq176 eq3016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3207 : x = (k y x) := by
    first
    | (have i₁ := eq1428 y
       have i₂ := eq3016
       grind)
    | exact superpose eq3016 eq1428
    | exact resolve eq1428 eq3016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428 eq3016
  have eq3446 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq833
       have i₂ := eq3207
       grind)
    | exact superpose eq3207 eq833
    | exact resolve eq833 eq3207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833 eq3207
  have eq3451 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3446
       have i₂ := eq3194
       grind)
    | exact superpose eq3194 eq3446
    | exact resolve eq3446 eq3194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3446
  have eq3452 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq3451
  have eq3630 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq176 (σ y) (σ y)
       have i₂ := eq3452
       grind)
    | exact superpose eq3452 eq176
    | exact resolve eq176 eq3452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq3452
  have eq3700 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3630
       grind)
    | exact superpose eq3630 eq16
    | exact resolve eq16 eq3630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3630
  have eq3745 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq3700
       have i₂ := eq3194
       grind)
    | exact superpose eq3194 eq3700
    | exact resolve eq3700 eq3194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3194 eq3700
  have eq3746 : False := by grind
  exact eq3746

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_pyx_y_pyx_Equation854 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    grind
  have eq72 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq62 X0 X0 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq83 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X0 X0)
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq9
    | exact resolve eq9 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq95 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 (M.op X1 X0)
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq83
    | exact resolve eq83 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X1)
       have i₂ := eq95 X1 X0
       grind)
    | exact superpose eq95 eq13
    | (have j0 := eq13 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X0)
       have r₂ := eq95 X0 X1
       grind)
    | exact resolve eq13 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq127 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq575 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq578 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq755 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k X1 (τ (M.op X0 (σ X1)))) ∨ (M.op (σ X1) (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 (M.op X0 (σ X1))
       have i₂ := eq134 X0 (σ X1)
       grind)
    | exact superpose eq134 eq29
    | (have j1 := eq134 X0 (σ X1)
       grind)
    | exact resolve eq29 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq756 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (k X1 (σ (M.op X0 (τ X1)))) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (M.op X0 (τ X1))
       have i₂ := eq134 X0 (τ X1)
       grind)
    | exact superpose eq134 eq18
    | (have j1 := eq134 X0 (τ X1)
       grind)
    | exact resolve eq18 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq1103 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq95 (τ X0) (τ X0)
       grind)
    | exact superpose eq95 eq65
    | exact resolve eq65 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq1185 : ∀ X0 : G, (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) = (k X0 (τ (σ (M.op (τ (σ X0)) (τ (σ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (σ (M.op (τ (σ X0)) (τ (σ X0))))
       have i₂ := eq1103 (σ X0)
       grind)
    | exact superpose eq1103 eq29
    | exact resolve eq29 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq1197 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ X0))) = (k X0 (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq1185 X0
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq1185
    | exact resolve eq1185 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185
  have eq1218 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1197 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1197
    | exact resolve eq1197 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197
  have eq1251 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq1218 (σ X0)
       grind)
    | exact superpose eq1218 eq29
    | exact resolve eq29 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1218
  have eq3072 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq578 x y
       grind)
    | exact superpose eq578 eq16
    | (have j1 := eq578 x y
       grind)
    | exact resolve eq16 eq578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3074 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k X0 (τ (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1251 x
       have i₂ := eq578 x x
       grind)
    | exact superpose eq578 eq1251
    | (have j1 := eq578 X0 X0
       grind)
    | exact resolve eq1251 eq578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3075 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (k X0 X1)) (M.op X2 (σ X0)))) = X2 ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X1) (σ X0)
       have i₂ := eq578 X1 X0
       grind)
    | exact superpose eq578 eq9
    | (have j1 := eq578 X1 X0
       grind)
    | exact resolve eq9 eq578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3110 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq3130 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq578 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3131 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq578 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq3132 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq3131 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3131
  have eq3152 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq3110 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3110
  have eq3154 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k X0 (τ (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq3074 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3074
  have eq3158 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3152 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq3152
    | (have j0 := eq3152 X0
       grind)
    | exact resolve eq3152 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3152
  have eq3161 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3154 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq3154
    | (have j0 := eq3154 X0
       grind)
    | exact resolve eq3154 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3154
  have eq3178 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3132 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq3132
    | (have j0 := eq3132 (τ X0)
       grind)
    | exact resolve eq3132 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3132
  have eq3180 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3178 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3178
    | (have j0 := eq3178 X0
       grind)
    | exact resolve eq3178 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3178
  have eq3183 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3180 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3180
    | (have j0 := eq3180 X0
       grind)
    | exact resolve eq3180 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3180
  have eq3399 : ∀ X0 : G, (τ (k X0 X0)) = (k (τ X0) (τ (k X0 X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3161 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq3161
    | (have j0 := eq3161 (τ X0)
       grind)
    | exact resolve eq3161 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3161
  have eq3433 : ∀ X0 : G, (τ (k X0 X0)) = (τ (k X0 (k X0 X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3399 X0
       have i₂ := eq32 (k X0 X0) X0
       grind)
    | exact superpose eq32 eq3399
    | (have j0 := eq3399 X0
       grind)
    | exact resolve eq3399 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3399
  have eq3449 : ∀ X0 : G, (τ (k X0 X0)) = (τ (k X0 (k X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3433 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3433
    | (have j0 := eq3433 X0
       grind)
    | exact resolve eq3433 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3433
  have eq11421 : ∀ X0 : G, (σ (k (τ X0) (k (τ X0) (τ X0)))) = (M.op (σ (k (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3158 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3158
    | exact resolve eq3158 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3158
  have eq11498 : ∀ X0 : G, (σ (k (τ X0) (k (τ X0) (τ X0)))) = (M.op (k (σ (τ X0)) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11421 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq11421
    | (have j0 := eq11421 X0
       grind)
    | exact resolve eq11421 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11421
  have eq11524 : ∀ X0 : G, (M.op (k X0 X0) X0) = (σ (k (τ X0) (k (τ X0) (τ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11498 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11498
    | (have j0 := eq11498 X0
       grind)
    | exact resolve eq11498 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11498
  have eq11546 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11524 X0
       have i₂ := eq18 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq18 eq11524
    | (have j0 := eq11524 X0
       grind)
    | exact resolve eq11524 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq11524
  have eq11564 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k X0 (k (σ (τ X0)) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11546 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq11546
    | (have j0 := eq11546 X0
       grind)
    | exact resolve eq11546 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11546
  have eq11580 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11564 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11564
    | (have j0 := eq11564 X0
       grind)
    | exact resolve eq11564 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11564
  have eq11650 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3449 X0
       have i₂ := eq11580 X0
       grind)
    | exact superpose eq11580 eq3449
    | (have j0 := eq3449 X0
       have j1 := eq11580 X0
       grind)
    | exact resolve eq3449 eq11580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3449 eq11580
  have eq11713 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11650 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11650
  have eq11933 : ∀ X0 : G, (τ (σ (k X0 X0))) = (τ (M.op (σ (k X0 X0)) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq11713 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq11713
    | (have j0 := eq11713 (σ X0)
       grind)
    | exact resolve eq11713 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11713
  have eq12051 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (τ (M.op (σ (k X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq11933 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq11933
    | (have j0 := eq11933 X0
       grind)
    | exact resolve eq11933 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11933
  have eq15905 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (k X0 X0) = (τ (M.op (σ (k X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1251 X0
       have i₂ := eq12051 X0
       grind)
    | exact superpose eq12051 eq1251
    | (have j1 := eq12051 X0
       grind)
    | exact resolve eq1251 eq12051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251 eq12051
  have eq15998 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ (k X0 X0)) (σ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15905 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15905
    | (have j0 := eq15905 X0
       grind)
    | exact resolve eq15905 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15905
  have eq16027 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15998 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq15998
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq15998 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16143 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq16027 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16027
  have eq83789 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq575 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq575
    | exact resolve eq575 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq83989 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq83789 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq83789
    | (have j0 := eq83789 X0 X1
       grind)
    | exact resolve eq83789 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83789
  have eq84113 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15998 X0
       have i₂ := eq83989 X0 X0
       grind)
    | exact superpose eq83989 eq15998
    | (have j0 := eq15998 X0
       have j1 := eq83989 X0 X0
       grind)
    | exact resolve eq15998 eq83989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15998
  have eq84344 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq84113 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84113
  have eq84402 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq84344 X0
       have j1 := eq3183 X0
       grind)
    | (have r₁ := eq84344 X0
       have r₂ := eq3183 X0
       grind)
    | exact resolve eq84344 eq3183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3183 eq84344
  have eq84500 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16143 X0
       have i₂ := eq84402 X0
       grind)
    | exact superpose eq84402 eq16143
    | (have j0 := eq16143 X0
       have j1 := eq84402 X0
       grind)
    | exact resolve eq16143 eq84402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16143 eq84402
  have eq84624 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq84500 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84500
  have eq84972 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq84624 (σ X0)
       grind)
    | exact superpose eq84624 eq15
    | (have j1 := eq84624 (σ X0)
       grind)
    | exact resolve eq15 eq84624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84624
  have eq85928 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  clear eq84972
  have eq86069 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq85928 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq85928
    | (have j0 := eq85928 X0
       grind)
    | exact resolve eq85928 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85928
  have eq86070 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq86069 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86069
  have eq86142 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq86070 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq86070
    | exact resolve eq86070 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86310 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq95 (σ X0) (σ X0)
       have i₂ := eq86070 X0
       grind)
    | exact superpose eq86070 eq95
    | exact resolve eq95 eq86070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86464 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq86142 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq86142
    | exact resolve eq86142 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86142
  have eq86509 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq86464 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq86464
    | exact resolve eq86464 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86464
  have eq90140 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq86310 X0
       have i₂ := eq86509 X0
       grind)
    | exact superpose eq86509 eq86310
    | exact resolve eq86310 eq86509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86310
  have eq115628 : ∀ X0 X1 : G, (k (σ X0) X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ X0)) ∨ (σ (τ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3130 (τ X1) X0
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq3130
    | (have j0 := eq3130 (τ X1) X0
       grind)
    | exact resolve eq3130 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3130
  have eq115753 : ∀ X0 X1 : G, (k (σ X0) X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ X0)) ∨ (σ (τ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq115628 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq115628
    | (have j0 := eq115628 X0 X1
       grind)
    | exact resolve eq115628 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115628
  have eq115824 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = X1 ∨ (k (σ X0) X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq115753 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq115753
    | (have j0 := eq115753 X0 X1
       grind)
    | exact resolve eq115753 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115753
  have eq115895 : ∀ X0 X1 : G, (σ (τ X1)) = (σ (k X0 X0)) ∨ (M.op X1 (σ X0)) = X1 ∨ (k (σ X0) X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq115824 X0 X1
       have i₂ := eq86070 X0
       grind)
    | exact superpose eq86070 eq115824
    | (have j0 := eq115824 X0 X1
       grind)
    | exact resolve eq115824 eq86070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115824
  have eq115958 : ∀ X0 X1 : G, (σ (τ X1)) = (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = X1 ∨ (k (σ X0) X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq115895 X0 X1
       have i₂ := eq86509 X0
       grind)
    | exact superpose eq86509 eq115895
    | (have j0 := eq115895 X0 X1
       grind)
    | exact resolve eq115895 eq86509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115895
  have eq116018 : ∀ X0 X1 : G, (k (σ X0) X1) ≠ X1 ∨ (M.op X1 (σ X0)) = X1 ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq115958 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq115958
    | (have j0 := eq115958 X0 X1
       grind)
    | exact resolve eq115958 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115958
  have eq121432 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq116018 X0 (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq116018
    | (have j0 := eq116018 X0 (σ X1)
       grind)
    | exact resolve eq116018 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116018
  have eq135467 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3072
       have i₂ := eq83989 x y
       grind)
    | exact superpose eq83989 eq3072
    | (have j1 := eq83989 (σ x) (σ y)
       grind)
    | (have r₁ := eq3072
       have r₂ := eq83989 x y
       grind)
    | exact resolve eq3072 eq83989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3072 eq83989
  have eq135468 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq135467
  have eq135470 : (σ x) = (σ (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq135468
       have i₂ := eq86070 y
       grind)
    | exact superpose eq86070 eq135468
    | exact resolve eq135468 eq86070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135468
  have eq135472 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq135470
       have i₂ := eq86509 y
       grind)
    | exact superpose eq86509 eq135470
    | exact resolve eq135470 eq86509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135470
  have eq152282 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (τ (k X0 X1))) (M.op X2 (σ (τ X0))))) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3075 (τ X0) (τ X1) X2
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq3075
    | (have j0 := eq3075 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq3075 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq3075
  have eq152817 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (τ (k X0 X1))) (M.op X2 X0))) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq152282 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq152282
    | (have j0 := eq152282 X0 X1 X2
       grind)
    | exact resolve eq152282 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152282
  have eq153017 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (k X0 X1) (M.op X2 X0))) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq152817 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq152817
    | (have j0 := eq152817 X0 X1 X2
       grind)
    | exact resolve eq152817 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152817
  have eq153162 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X2 (M.op (k X0 X1) (M.op X2 X0))) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq153017 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq153017
    | (have j0 := eq153017 X0 X1 X2
       grind)
    | exact resolve eq153017 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153017
  have eq153288 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (M.op X2 (M.op (k X0 X1) (M.op X2 X0))) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq153162 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq153162
    | (have j0 := eq153162 X0 X1 X2
       grind)
    | exact resolve eq153162 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153162
  have eq153387 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (σ (k (τ X0) (τ X0))) ∨ (M.op X1 X0) = X1 ∨ (M.op X2 (M.op (k X0 X1) (M.op X2 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq153288 X0 X1 X2
       have i₂ := eq86070 (τ X0)
       grind)
    | exact superpose eq86070 eq153288
    | (have j0 := eq153288 X0 X1 X2
       grind)
    | exact resolve eq153288 eq86070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153288
  have eq153465 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (k (σ (τ X0)) X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X2 (M.op (k X0 X1) (M.op X2 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq153387 X0 X1 X2
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq153387
    | (have j0 := eq153387 X0 X1 X2
       grind)
    | exact resolve eq153387 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq153387
  have eq153521 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (k X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X2 (M.op (k X0 X1) (M.op X2 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq153465 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq153465
    | (have j0 := eq153465 X0 X1 X2
       grind)
    | exact resolve eq153465 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153465
  have eq153565 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op X1 X0) = X1 ∨ (M.op X2 (M.op (k X0 X1) (M.op X2 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq153521 X0 X1 X2
       have i₂ := eq86509 X0
       grind)
    | exact superpose eq86509 eq153521
    | (have j0 := eq153521 X0 X1 X2
       grind)
    | exact resolve eq153521 eq86509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153521
  have eq153598 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (k X0 X1) (M.op X2 X0))) = X2 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq153565 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq153565
    | (have j0 := eq153565 X0 X1 X2
       grind)
    | exact resolve eq153565 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153565
  have eq208990 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 (k X0 X1)
       have i₂ := eq153598 X0 X1 X0
       grind)
    | exact superpose eq153598 eq83
    | (have j1 := eq153598 X0 X1 x
       grind)
    | exact resolve eq83 eq153598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq153598
  have eq1478535 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (k (σ X0) (σ (M.op X1 X0))) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq756 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq756
    | exact resolve eq756 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq1479556 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (σ (k X0 (M.op X1 X0))) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1478535 X0 X1
       have i₂ := eq15 X0 (M.op X1 X0)
       grind)
    | exact superpose eq15 eq1478535
    | (have j0 := eq1478535 X0 X1
       grind)
    | exact resolve eq1478535 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1478535
  have eq5236093 : (σ x) = (σ (k y x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1479556 y x
       have i₂ := eq135472
       grind)
    | exact superpose eq135472 eq1479556
    | exact resolve eq1479556 eq135472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135472 eq1479556
  have eq5236111 : (σ x) = (σ (k y x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq5236093
  have eq5236132 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have j1 := eq121432 y x
       grind)
    | (have r₁ := eq5236111
       have r₂ := eq121432 y x
       grind)
    | exact resolve eq5236111 eq121432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121432 eq5236111
  have eq5236171 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5236132
       grind)
    | exact superpose eq5236132 eq16
    | exact resolve eq16 eq5236132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5236172 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq755 (σ x) y
       have i₂ := eq5236132
       grind)
    | exact superpose eq5236132 eq755
    | exact resolve eq755 eq5236132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755 eq5236132
  have eq5236773 : x = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq5236172
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5236172
    | exact resolve eq5236172 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5236172
  have eq5236888 : (σ x) = (σ (k y y)) ∨ x = (k y x) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq5236773
       have i₂ := eq86070 y
       grind)
    | exact superpose eq86070 eq5236773
    | exact resolve eq5236773 eq86070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86070 eq5236773
  have eq5236945 : (σ x) = (σ (M.op y y)) ∨ x = (k y x) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq5236888
       have i₂ := eq86509 y
       grind)
    | exact superpose eq86509 eq5236888
    | exact resolve eq5236888 eq86509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86509 eq5236888
  have eq5236946 : x = (k y x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq5236945
  have eq5237030 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq208990 y x
       have i₂ := eq5236946
       grind)
    | exact superpose eq5236946 eq208990
    | (have j0 := eq208990 y x
       grind)
    | exact resolve eq208990 eq5236946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208990 eq5236946
  have eq5237061 : x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq5237030
  have eq5237394 : (σ x) ≠ (σ x) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq5236171
       have i₂ := eq5237061
       grind)
    | exact superpose eq5237061 eq5236171
    | exact resolve eq5236171 eq5237061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5236171 eq5237061
  have eq5237398 : (σ x) ≠ (σ x) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq5237394
  have eq5237399 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq5237398
  have eq5237721 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq5237399
       grind)
    | exact superpose eq5237399 eq10
    | exact resolve eq10 eq5237399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5237399
  have eq5238984 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq5237721
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5237721
    | exact resolve eq5237721 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5237721
  have eq5238985 : x = (M.op y y) := by grind
  clear eq5238984
  have eq5239439 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq90140 y
       have i₂ := eq5238985
       grind)
    | exact superpose eq5238985 eq90140
    | exact resolve eq90140 eq5238985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90140
  have eq5240494 : x = (M.op x y) := by
    first
    | (have i₁ := eq95 y y
       have i₂ := eq5238985
       grind)
    | exact superpose eq5238985 eq95
    | exact resolve eq95 eq5238985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq5238985
  have eq5243051 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5239439
       grind)
    | exact superpose eq5239439 eq16
    | exact resolve eq16 eq5239439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5239439
  have eq5243720 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq5243051
       have i₂ := eq5240494
       grind)
    | exact superpose eq5240494 eq5243051
    | exact resolve eq5243051 eq5240494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5240494 eq5243051
  have eq5243721 : False := by grind
  exact eq5243721

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pxx_pxy_pyx_Equation854 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (M.op X0 y))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq74
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq95
    | exact resolve eq95 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq97 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
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
  have eq110 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq110 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq110 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq110 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq115 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq111 y
       grind)
    | exact superpose eq111 eq75
    | exact resolve eq75 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq116 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq111 sF2
       grind)
    | exact superpose eq111 eq49
    | exact resolve eq49 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq117 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq116
       have i₂ := eq111 x
       grind)
    | exact superpose eq111 eq116
    | exact resolve eq116 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq118 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq115
       have i₂ := eq111 sF3
       grind)
    | exact superpose eq111 eq115
    | exact resolve eq115 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq138 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq141 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq138
       have i₂ := eq111 sF1
       grind)
    | exact superpose eq111 eq138
    | exact resolve eq138 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq144 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq141
       have i₂ := eq111 sF0
       grind)
    | exact superpose eq111 eq141
    | exact resolve eq141 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq141
  have eq166 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq144 eq16
    | exact resolve eq16 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq253 : x = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260 : (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ x)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq516 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 X0 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq523 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X0 X0)
       have i₂ := eq516 X0
       grind)
    | exact superpose eq516 eq14
    | exact resolve eq14 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq1320 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq50 eq523
    | exact resolve eq523 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1322 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq51 eq523
    | exact resolve eq523 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq523
  have eq11171 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11172 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq11171
    | exact resolve eq11171 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11171
  have eq11183 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11172
       have r₂ := eq27
       grind)
    | exact resolve eq11172 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11172
  have eq11187 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq11183
    | exact resolve eq11183 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11183
  have eq11189 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq11187
    | exact resolve eq11187 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11187
  have eq11192 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11189 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq11189
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq11189
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq11189
       grind)
    | exact resolve eq12 eq11189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11189
  have eq11229 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11192
       have r₂ := eq26
       grind)
    | exact resolve eq11192 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11192
  have eq11231 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq11229
    | exact resolve eq11229 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11229
  have eq11232 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq11231
  have eq11314 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11232 eq98
    | exact resolve eq98 eq11232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq11232
  have eq11322 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11314
  have eq11324 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11322
       have r₂ := eq27
       grind)
    | exact resolve eq11322 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11322
  have eq11327 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq11324
       grind)
    | exact superpose eq11324 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq11324
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq11324
       grind)
    | exact resolve eq12 eq11324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11324
  have eq11364 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11327
       have r₂ := eq18
       grind)
    | exact resolve eq11327 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11327
  have eq11366 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11364
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11364
    | exact resolve eq11364 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11364
  have eq11367 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11366
  have eq11697 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11367
       grind)
    | exact superpose eq11367 eq74
    | exact resolve eq74 eq11367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq11367
  have eq11711 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq11697
    | exact resolve eq11697 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11697
  have eq11764 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11711 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq11711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11767 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11764
    | exact resolve eq11764 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11764
  have eq11778 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11767
       have r₂ := eq27
       grind)
    | exact resolve eq11767 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11767
  have eq11782 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11778
    | exact resolve eq11778 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11778
  have eq11784 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11782
    | exact resolve eq11782 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11782
  have eq11785 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11784
  have eq11789 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11785 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq11785
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq11785
       grind)
    | exact resolve eq12 eq11785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11785
  have eq11826 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11789
       have r₂ := eq26
       grind)
    | exact resolve eq11789 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11789
  have eq11828 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq11826
    | exact resolve eq11826 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11826
  have eq11829 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11828
  have eq11919 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11829 eq11711
    | exact resolve eq11711 eq11829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11711 eq11829
  have eq11921 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11919
  have eq11925 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11921
       have r₂ := eq27
       grind)
    | exact resolve eq11921 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11921
  have eq11931 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11925 eq260
    | exact resolve eq260 eq11925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq11954 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11925 eq1322
    | exact resolve eq1322 eq11925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322
  have eq12272 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11954 eq11931
    | exact resolve eq11931 eq11954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11931
  have eq12310 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq12272
  have eq12312 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq12310
    | exact resolve eq12310 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12310
  have eq12348 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12312 eq11925
    | exact resolve eq11925 eq12312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11925 eq12312
  have eq12351 : (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq12348
  have eq12359 : y = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12351 eq29
    | exact resolve eq29 eq12351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq12441 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12351 eq11954
    | exact resolve eq11954 eq12351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11954 eq12351
  have eq12444 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq12441
  have eq12505 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq12359
    | exact resolve eq12359 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12359
  have eq12520 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq12505 eq20
    | exact resolve eq20 eq12505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12597 : y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq12505 eq1320
    | exact resolve eq1320 eq12505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320
  have eq12666 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12520
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12520
    | exact resolve eq12520 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12520
  have eq13030 : (τ (σ x)) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12444 eq117
    | exact resolve eq117 eq12444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq12444
  have eq13113 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq13030
    | exact resolve eq13030 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq13030
  have eq13121 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq118
       have i₂ := eq12597
       grind)
    | exact superpose eq12597 eq118
    | exact resolve eq118 eq12597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq12597
  have eq13226 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq13121
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13121
    | exact resolve eq13121 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13121
  have eq13439 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq12666 eq13226
    | exact resolve eq13226 eq12666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12666 eq13226
  have eq13510 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq13439
  have eq13556 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq13510 eq166
    | exact resolve eq166 eq13510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13510
  have eq13636 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq30 eq13556
    | exact resolve eq13556 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq13556
  have eq13692 : x = (M.op x (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq13636 eq253
    | exact resolve eq253 eq13636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253 eq13636
  have eq14114 : x = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq12505 eq13692
    | exact resolve eq13692 eq12505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13692
  have eq14153 : x = (M.op x y) ∨ x = y := by grind
  clear eq14114
  have eq14154 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq14153
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14153
    | exact resolve eq14153 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14153
  have eq14242 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq14154 eq12505
    | exact resolve eq12505 eq14154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12505 eq14154
  have eq14249 : x = y := by grind
  clear eq14242
  have eq14626 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq14249
       grind)
    | exact superpose eq14249 eq18
    | exact resolve eq18 eq14249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq14627 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq14249
       grind)
    | exact superpose eq14249 eq24
    | exact resolve eq24 eq14249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq14756 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq14627
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14627
    | exact resolve eq14627 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14627
  have eq14774 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq14756 eq26
    | exact resolve eq26 eq14756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq14756
  have eq15793 : x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13113
       have i₂ := eq14626
       grind)
    | exact superpose eq14626 eq13113
    | exact resolve eq13113 eq14626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13113
  have eq15845 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15793
       have i₂ := eq14249
       grind)
    | exact superpose eq14249 eq15793
    | exact resolve eq15793 eq14249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14249 eq15793
  have eq15846 : x = (M.op x y) := by grind
  clear eq15845
  have eq15865 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq15846 eq20
    | exact resolve eq20 eq15846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq16028 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq15865
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15865
    | exact resolve eq15865 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15865
  have eq18080 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq16028 eq14774
    | exact resolve eq14774 eq16028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14774
  have eq18219 : (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq18080 eq166
    | exact resolve eq166 eq18080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166 eq18080
  have eq18287 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq15846 eq18219
    | exact resolve eq18219 eq15846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18219
  have eq18299 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq18287
       have i₂ := eq14626
       grind)
    | exact superpose eq14626 eq18287
    | exact resolve eq18287 eq14626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14626 eq18287
  have eq18306 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq15846 eq18299
    | exact resolve eq18299 eq15846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15846 eq18299
  have eq18335 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18306 eq15
    | exact resolve eq15 eq18306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18306
  have eq18392 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18335
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18335
    | exact resolve eq18335 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq18335
  have eq18411 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16028 eq18392
    | exact resolve eq18392 eq16028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16028 eq18392
  have eq18426 : False := by grind
  exact eq18426
