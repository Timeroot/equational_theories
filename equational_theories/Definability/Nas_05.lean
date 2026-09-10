import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3912`: `x ◇ x = (y ◇ (z ◇ w)) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation3912 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3912 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3912.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X3)) X3) := by
    intro X0 X1 X2 X3
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
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
  have eq36 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op x y)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq28 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 X3 X5 : G, (M.op X3 X3) = (M.op (M.op (M.op X0 (M.op X1 X2)) X2) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X3 (M.op x X5) x X5
       have i₂ := eq14 (M.op x X5) X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X5 : G, (M.op X1 X1) = (M.op (M.op X0 X0) X5) := by
    intro X0 X1 X5
    first
    | (have i₁ := eq14 X1 (M.op x (M.op x (M.op x X5))) x X5
       have i₂ := eq14 X0 x x (M.op x X5)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x x x
       have i₂ := eq14 X1 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
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
  clear eq46
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq91
    | exact resolve eq91 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22 eq99
    | exact resolve eq99 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq105 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq123 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op X1 (M.op X0 X0)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X1 := by
    intro X0 X1
    grind
  have eq257 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 X1 (M.op x X3) x X3
       have i₂ := eq56 (M.op x X3) X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    grind
  have eq1161 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X0
       have i₂ := eq59 (σ X0) X1
       grind)
    | (have i₁ := eq86 X0 X0
       have i₂ := eq59 X0 (σ X0)
       grind)
    | exact superpose eq59 eq86
    | exact resolve eq86 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1198 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1161 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161
  have eq1633 : ∀ X0 X1 X2 X4 X5 : G, (M.op X2 X2) = (M.op (M.op (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) X1) X4) X5) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq57 (M.op x X4) x X4 X2 X5
       have i₂ := eq257 X0 (M.op x X4) X1
       grind)
    | (have i₁ := eq57 (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) X1 X2 x X5
       have i₂ := eq257 X0 X1 (M.op X1 X2)
       grind)
    | exact superpose eq257 eq57
    | exact resolve eq57 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq257
  have eq8555 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X1 (τ X1)
       have i₂ := eq1198 X0 (τ X1)
       grind)
    | exact superpose eq1198 eq36
    | (have j1 := eq1198 X0 (τ X1)
       grind)
    | exact resolve eq36 eq1198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1198
  have eq8584 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8555 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq8555
    | (have j0 := eq8555 X0 X1
       grind)
    | exact resolve eq8555 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8555
  have eq8592 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8584 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq8584
    | (have j0 := eq8584 X0 X1
       grind)
    | exact resolve eq8584 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8584
  have eq9419 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq8592 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8592
  have eq58700 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op (τ X1) (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq343 X1
       have i₂ := eq58 (τ X1) X0 (τ X1)
       grind)
    | exact superpose eq58 eq343
    | exact resolve eq343 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq158216 : ∀ X0 X1 X2 : G, (σ (M.op X1 X1)) = (k X2 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58700 X1 X2
       have i₂ := eq59 (τ X2) X0
       grind)
    | (have i₁ := eq58700 X1 X2
       have i₂ := eq59 X0 (τ X2)
       grind)
    | exact superpose eq59 eq58700
    | exact resolve eq58700 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158271 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq58700 X0 x
       have i₂ := eq58700 X1 x
       grind)
    | exact superpose eq58700 eq58700
    | exact resolve eq58700 eq58700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58700
  have eq159829 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op X2 X2) = (σ (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9419 X2 (σ (M.op X1 X1))
       have i₂ := eq158216 X1 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq158216 eq9419
    | (have j0 := eq9419 X2 (σ (M.op X1 X1))
       grind)
    | (have r₁ := eq9419 X0 (σ (M.op X1 X1))
       have r₂ := eq158216 X1 X1 (σ (M.op X1 X1))
       grind)
    | exact resolve eq9419 eq158216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9419 eq158216
  have eq159883 : ∀ X1 X2 : G, (M.op X2 X2) = (σ (M.op X1 X1)) := by
    intro X1 X2
    first
    | (have j0 := eq159829 x X1 X2
       grind)
    | (have r₁ := eq159829 x X1 X2
       have r₂ := eq158271 x X1
       grind)
    | (have r₁ := eq159829 X1 x X2
       have r₂ := eq158271 x X1
       grind)
    | exact resolve eq159829 eq158271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158271 eq159829
  have eq160167 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq159883 x X1
       have i₂ := eq55 x X0
       grind)
    | exact superpose eq55 eq159883
    | exact resolve eq159883 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq160170 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq159883 x X2
       have i₂ := eq58 X0 x X1
       grind)
    | (have i₁ := eq159883 (M.op X0 X0) X2
       have i₂ := eq58 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq58 eq159883
    | exact resolve eq159883 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160973 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X1 X1)
       have i₂ := eq159883 X1 X0
       grind)
    | exact superpose eq159883 eq16
    | exact resolve eq16 eq159883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161273 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (τ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq160973 x X2
       have i₂ := eq58 X0 x X1
       grind)
    | (have i₁ := eq160973 (M.op X0 X0) X1
       have i₂ := eq58 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq58 eq160973
    | exact resolve eq160973 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq201726 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq100 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq201733 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq28 eq201726
    | exact resolve eq201726 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201726
  have eq201744 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq201733
       have r₂ := eq29
       grind)
    | exact resolve eq201733 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201733
  have eq201829 : ∀ X0 : G, (M.op X0 X0) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq201744 eq160973
    | exact resolve eq160973 eq201744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160973 eq201744
  have eq201923 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = y ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq31 eq201829
    | exact resolve eq201829 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201829
  have eq203476 : ∀ X0 X1 : G, y = (M.op x x) ∨ (M.op X1 X1) = y ∨ x = (M.op y y) ∨ (M.op X0 X0) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq201923 X0
       have i₂ := eq59 sF3 X1
       grind)
    | (have i₁ := eq201923 X0
       have i₂ := eq59 X0 sF3
       grind)
    | exact superpose eq59 eq201923
    | (have j0 := eq201923 x
       grind)
    | exact resolve eq201923 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201923
  have eq206458 : ∀ X0 : G, y ≠ y ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq203476 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203476
  have eq206460 : ∀ X0 : G, y = (M.op x x) ∨ x = (M.op y y) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq206458 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206458
  have eq206484 : ∀ X0 X1 : G, x = (M.op y y) ∨ (M.op X0 X0) = y ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq206460 X1
       have i₂ := eq59 x X0
       grind)
    | (have i₁ := eq206460 X1
       have i₂ := eq59 X0 x
       grind)
    | exact superpose eq59 eq206460
    | (have j0 := eq206460 X1
       grind)
    | exact resolve eq206460 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq206460
  have eq206760 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ x) ∨ (M.op X1 X1) = y ∨ (σ x) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq159883 y X0
       have i₂ := eq206484 X1 X2
       grind)
    | exact superpose eq206484 eq159883
    | (have j1 := eq206484 X1 X0
       grind)
    | exact resolve eq159883 eq206484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159883 eq206484
  have eq206863 : ∀ X0 X1 X2 : G, (σ x) = (M.op X2 X2) ∨ (M.op X1 X1) = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq206760 X2 X1 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq206760
    | (have j0 := eq206760 X2 X1 X2
       grind)
    | exact resolve eq206760 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206760
  have eq211346 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (M.op X1 X1) = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0 X1
    first
    | (have j0 := eq206863 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206863
  have eq211347 : ∀ X0 X1 : G, (M.op X1 X1) = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0 X1
    first
    | (have j0 := eq211346 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211346
  have eq212156 : ∀ X0 X2 : G, (M.op X0 X0) = (σ y) ∨ (σ x) = (M.op X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq160170 x (M.op x x) X0
       have i₂ := eq211347 X2 (M.op x x)
       grind)
    | exact superpose eq211347 eq160170
    | (have j1 := eq211347 X2 x
       grind)
    | exact resolve eq160170 eq211347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211347
  have eq212375 : ∀ X0 X2 : G, (σ x) = (M.op X2 X2) ∨ (M.op X0 X0) = (σ y) := by
    intro X0 X2
    first
    | (have i₁ := eq212156 X0 X2
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq212156
    | (have j0 := eq212156 X0 X2
       grind)
    | exact resolve eq212156 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212156
  have eq214846 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 sF4
       have i₂ := eq212375 X0 sF4
       grind)
    | (have i₁ := eq56 X0 sF4
       have i₂ := eq212375 sF4 x
       grind)
    | exact superpose eq212375 eq56
    | (have j1 := eq212375 X1 x
       grind)
    | exact resolve eq56 eq212375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq214914 : ∀ X0 X2 : G, (M.op X0 X0) = (τ (σ x)) ∨ (σ y) = (M.op X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq161273 x (M.op x x) X0
       have i₂ := eq212375 X2 (M.op x x)
       grind)
    | (have i₁ := eq161273 X0 (M.op X0 X0) X2
       have i₂ := eq212375 (M.op X0 X0) X2
       grind)
    | exact superpose eq212375 eq161273
    | (have j1 := eq212375 X2 X2
       grind)
    | exact resolve eq161273 eq212375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212375
  have eq215131 : ∀ X0 X2 : G, (σ y) = (M.op X2 X2) ∨ (M.op X0 X0) = x := by
    intro X0 X2
    first
    | exact superpose eq30 eq214914
    | (have j0 := eq214914 X0 X2
       grind)
    | exact resolve eq214914 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214914
  have eq215162 : ∀ X0 X1 : G, (M.op X1 X1) = (σ y) ∨ (M.op X0 X0) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq28 eq214846
    | (have j0 := eq214846 X0 X1
       grind)
    | exact resolve eq214846 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214846
  have eq215946 : ∀ X0 X2 : G, (M.op X0 X0) = (τ (σ y)) ∨ x = (M.op X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq161273 x (M.op x x) X0
       have i₂ := eq215131 X2 (M.op x x)
       grind)
    | (have i₁ := eq161273 X0 (M.op X0 X0) X2
       have i₂ := eq215131 (M.op X0 X0) X2
       grind)
    | exact superpose eq215131 eq161273
    | (have j1 := eq215131 X2 X2
       grind)
    | exact resolve eq161273 eq215131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215131
  have eq216164 : ∀ X0 X2 : G, x = (M.op X2 X2) ∨ (M.op X0 X0) = y := by
    intro X0 X2
    first
    | exact superpose eq31 eq215946
    | (have j0 := eq215946 X0 X2
       grind)
    | exact resolve eq215946 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215946
  have eq216947 : ∀ X0 X2 : G, (M.op X0 X0) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq161273 x (M.op x x) X0
       have i₂ := eq215162 X2 (M.op x x)
       grind)
    | (have i₁ := eq161273 X0 (M.op X0 X0) X2
       have i₂ := eq215162 (M.op X0 X0) x
       grind)
    | exact superpose eq215162 eq161273
    | (have j1 := eq215162 X2 x
       grind)
    | exact resolve eq161273 eq215162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215162
  have eq217166 : ∀ X0 X2 : G, (M.op (σ x) (σ y)) = (M.op X2 X2) ∨ (M.op X0 X0) = y := by
    intro X0 X2
    first
    | exact superpose eq31 eq216947
    | (have j0 := eq216947 X0 X2
       grind)
    | exact resolve eq216947 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216947
  have eq217883 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq160167 sF0 X1
       have i₂ := eq216164 X0 sF0
       grind)
    | exact superpose eq216164 eq160167
    | (have j1 := eq216164 X1 x
       grind)
    | exact resolve eq160167 eq216164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160167 eq216164
  have eq218181 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq217883 X0 X1
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq217883
    | (have j0 := eq217883 X0 X1
       grind)
    | exact resolve eq217883 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217883
  have eq218238 : ∀ X0 X1 : G, (M.op X1 X1) = y ∨ (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq22 eq218181
    | (have j0 := eq218181 X0 X1
       grind)
    | exact resolve eq218181 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218181
  have eq221015 : ∀ X0 X2 : G, (M.op X0 X0) = (σ y) ∨ (σ (M.op x y)) = (M.op X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq160170 x (M.op x x) X0
       have i₂ := eq218238 X2 (M.op x x)
       grind)
    | exact superpose eq218238 eq160170
    | (have j1 := eq218238 X2 x
       grind)
    | exact resolve eq160170 eq218238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218238
  have eq221238 : ∀ X0 X2 : G, (σ (M.op x y)) = (M.op X2 X2) ∨ (M.op X0 X0) = (σ y) := by
    intro X0 X2
    first
    | (have i₁ := eq221015 X0 X2
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq221015
    | (have j0 := eq221015 X0 X2
       grind)
    | exact resolve eq221015 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221015
  have eq225416 : ∀ X1 X2 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op X1 X1) = y ∨ (σ y) = (M.op X2 X2) := by
    intro X1 X2
    first
    | (have i₁ := eq217166 X1 x
       have i₂ := eq221238 X2 x
       grind)
    | (have i₁ := eq217166 x x
       have i₂ := eq221238 x X2
       grind)
    | exact superpose eq221238 eq217166
    | (have j0 := eq217166 X1 X2
       have j1 := eq221238 X2 X2
       grind)
    | exact resolve eq217166 eq221238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217166 eq221238
  have eq226010 : ∀ X1 X2 : G, (σ y) = (M.op X2 X2) ∨ (M.op X1 X1) = y := by
    intro X1 X2
    first
    | (have j0 := eq225416 X1 X2
       grind)
    | (have r₁ := eq225416 X1 X2
       have r₂ := eq29
       grind)
    | exact resolve eq225416 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225416
  have eq226804 : ∀ X0 X2 : G, (M.op X0 X0) = (τ (σ y)) ∨ y = (M.op X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq161273 x (M.op x x) X0
       have i₂ := eq226010 X2 (M.op x x)
       grind)
    | (have i₁ := eq161273 X0 (M.op X0 X0) X2
       have i₂ := eq226010 (M.op X0 X0) X2
       grind)
    | exact superpose eq226010 eq161273
    | (have j1 := eq226010 X2 X2
       grind)
    | exact resolve eq161273 eq226010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226010
  have eq227026 : ∀ X0 X2 : G, y = (M.op X2 X2) ∨ (M.op X0 X0) = y := by
    intro X0 X2
    first
    | exact superpose eq31 eq226804
    | (have j0 := eq226804 X0 X2
       grind)
    | exact resolve eq226804 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq226804
  have eq228037 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq227026 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227026
  have eq228038 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq228037 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228037
  have eq228855 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq160170 x (M.op x x) X0
       have i₂ := eq228038 (M.op x x)
       grind)
    | exact superpose eq228038 eq160170
    | exact resolve eq160170 eq228038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160170
  have eq228857 : ∀ X0 : G, (M.op X0 X0) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq161273 x (M.op x x) X0
       have i₂ := eq228038 (M.op x x)
       grind)
    | exact superpose eq228038 eq161273
    | exact resolve eq161273 eq228038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161273
  have eq229159 : y = (τ y) := by
    first
    | (have i₁ := eq228857 x
       have i₂ := eq228038 x
       grind)
    | exact superpose eq228038 eq228857
    | exact resolve eq228857 eq228038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228857
  have eq229161 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq228855 X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq228855
    | (have j0 := eq228855 X0
       grind)
    | exact resolve eq228855 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228855
  have eq229528 : y = (σ y) := by
    first
    | (have i₁ := eq229161 x
       have i₂ := eq228038 x
       grind)
    | exact superpose eq228038 eq229161
    | exact resolve eq229161 eq228038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229161
  have eq229583 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq229528 eq28
    | exact resolve eq28 eq229528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234832 : ∀ X0 X1 X2 X4 X5 : G, (M.op X2 X2) = (M.op (M.op (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) y) X1) X4) X5) := by
    intro X0 X1 X2 X4 X5
    first
    | exact superpose eq229528 eq1633
    | exact resolve eq1633 eq229528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1633
  have eq234833 : ∀ X0 X1 X4 X5 : G, y = (M.op (M.op (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) y) X1) X4) X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq234832 X0 X1 x X4 X5
       have i₂ := eq228038 x
       grind)
    | exact superpose eq228038 eq234832
    | exact resolve eq234832 eq228038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234832
  have eq236066 : ∀ X3 : G, (M.op X3 y) = (k y X3) ∨ (M.op y y) = X3 := by
    intro X3
    first
    | exact superpose eq234833 eq123
    | exact resolve eq123 eq234833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq234833
  have eq236988 : ∀ X3 : G, (M.op X3 y) = (k y X3) ∨ y = X3 := by
    intro X3
    first
    | (have i₁ := eq236066 X3
       have i₂ := eq228038 y
       grind)
    | exact superpose eq228038 eq236066
    | (have j0 := eq236066 X3
       grind)
    | exact resolve eq236066 eq228038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236066
  have eq260740 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq105
       have i₂ := eq236988 x
       grind)
    | exact superpose eq236988 eq105
    | (have j1 := eq236988 x
       grind)
    | exact resolve eq105 eq236988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq260792 : (σ (M.op x y)) = (k y (σ x)) ∨ x = y := by
    first
    | exact superpose eq229528 eq260740
    | exact resolve eq260740 eq229528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260740
  have eq260852 : (σ (M.op x y)) = (k y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq260792
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq260792
    | exact resolve eq260792 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260792
  have eq260893 : (σ (M.op x y)) = (k y (σ x)) ∨ x = y := by
    first
    | exact superpose eq22 eq260852
    | exact resolve eq260852 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260852
  have eq260929 : (σ (M.op x y)) = (M.op (σ x) y) ∨ y = (σ x) ∨ x = y := by
    first
    | exact superpose eq260893 eq236988
    | (have j0 := eq236988 (σ x)
       grind)
    | exact resolve eq236988 eq260893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236988 eq260893
  have eq260943 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (σ x) ∨ x = y := by
    first
    | exact superpose eq229583 eq260929
    | exact resolve eq260929 eq229583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229583 eq260929
  have eq260954 : y = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq260943
       have r₂ := eq29
       grind)
    | exact resolve eq260943 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260943
  have eq260962 : x = (τ y) ∨ x = y := by
    first
    | exact superpose eq260954 eq30
    | exact resolve eq30 eq260954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq260954
  have eq261110 : x = y ∨ x = y := by
    first
    | (have i₁ := eq260962
       have i₂ := eq229159
       grind)
    | exact superpose eq229159 eq260962
    | exact resolve eq260962 eq229159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229159 eq260962
  have eq261111 : x = y := by grind
  clear eq261110
  have eq261198 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq261111
       grind)
    | exact superpose eq261111 eq20
    | exact resolve eq20 eq261111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261199 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq261111
       grind)
    | exact superpose eq261111 eq26
    | exact resolve eq26 eq261111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq261428 : y = (σ x) := by
    first
    | exact superpose eq229528 eq261199
    | exact resolve eq261199 eq229528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261199
  have eq261429 : y = (M.op x y) := by
    first
    | (have i₁ := eq261198
       have i₂ := eq228038 x
       grind)
    | exact superpose eq228038 eq261198
    | exact resolve eq261198 eq228038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228038 eq261198
  have eq261523 : y = (σ x) := by
    first
    | (have i₁ := eq261428
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq261428
    | exact resolve eq261428 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261428
  have eq261524 : x = (M.op x y) := by
    first
    | (have i₁ := eq261429
       have i₂ := eq261111
       grind)
    | exact superpose eq261111 eq261429
    | exact resolve eq261429 eq261111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261429
  have eq261600 : x = (σ x) := by
    first
    | (have i₁ := eq261523
       have i₂ := eq261111
       grind)
    | exact superpose eq261111 eq261523
    | exact resolve eq261523 eq261111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261111 eq261523
  have eq261660 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq261524 eq22
    | exact resolve eq22 eq261524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq261872 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq261660
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq261660
    | exact resolve eq261660 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq261660
  have eq262046 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq261600 eq28
    | exact resolve eq28 eq261600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq262197 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq229528 eq262046
    | exact resolve eq262046 eq229528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229528 eq262046
  have eq262232 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq262197
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq262197
    | exact resolve eq262197 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq262197
  have eq262251 : x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq261524 eq262232
    | exact resolve eq262232 eq261524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261524 eq262232
  have eq262258 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq261600 eq261872
    | exact resolve eq261872 eq261600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261600 eq261872
  have eq262261 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq262251 eq29
    | exact resolve eq29 eq262251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq262251
  have eq262698 : False := by grind
  exact eq262698

/-- `Equation3912`: `x ◇ x = (y ◇ (z ◇ w)) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pyx_pyx_pxy_Equation3912 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3912 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3912.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X3)) X3) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq13 (k X1 X1) X1
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq48 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq48
    | (have j0 := eq48 x
       grind)
    | exact resolve eq48 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq177 : ∀ X0 X1 X2 X5 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X0 X0)) X5) := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq16 X1 X2 (M.op x (M.op x X5)) X5
       have i₂ := eq16 X0 x x X5
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op x y)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 X1 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X5 : G, (M.op X1 X1) = (M.op (M.op X0 X0) X5) := by
    intro X0 X1 X5
    first
    | (have i₁ := eq16 X1 (M.op x (M.op x (M.op x X5))) x X5
       have i₂ := eq16 X0 x x (M.op x X5)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x x x
       have i₂ := eq16 X1 x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X2 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X2
    first
    | (have i₁ := eq179 x X2
       have i₂ := eq179 x X0
       grind)
    | exact superpose eq179 eq179
    | exact resolve eq179 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq181 X3 x X4
       have i₂ := eq181 X0 x X1
       grind)
    | (have i₁ := eq181 X0 (M.op X0 X0) x
       have i₂ := eq181 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq181 eq181
    | exact resolve eq181 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq399 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq456 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq483 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq399 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq399
    | exact resolve eq399 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq586 : ∀ X0 : G, (τ (k (k (σ y) (σ y)) X0)) = (k (k y y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq116 eq483
    | exact resolve eq483 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq666 : ∀ X0 X1 X2 X4 X5 X6 : G, (M.op (M.op X4 (M.op X5 X6)) X6) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
    intro X0 X1 X2 X4 X5 X6
    first
    | (have i₁ := eq16 x X4 X5 X6
       have i₂ := eq177 X1 x X0 X2
       grind)
    | (have i₁ := eq16 (M.op X2 (M.op X0 X0)) X1 X2 x
       have i₂ := eq177 X0 X1 X2 (M.op X2 (M.op X0 X0))
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq184 X0
       have i₂ := eq182 X0 X1
       grind)
    | (have i₁ := eq184 X1
       have i₂ := eq182 X0 X1
       grind)
    | exact superpose eq182 eq184
    | exact resolve eq184 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1573 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) = (M.op (k (M.op X0 X0) X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq177 X0 X2 X1 X3
       have i₂ := eq696 X0 X1
       grind)
    | exact superpose eq696 eq177
    | exact resolve eq177 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq696
  have eq1753 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X2 X1
       have i₂ := eq182 X1 X0
       grind)
    | (have i₁ := eq28 X2 X1
       have i₂ := eq182 X0 X1
       grind)
    | exact superpose eq182 eq28
    | (have j0 := eq28 X2 X1
       grind)
    | (have r₁ := eq28 X0 (M.op X1 X1)
       have r₂ := eq182 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq28 X0 (M.op X0 X0)
       have r₂ := eq182 X0 (M.op X0 X0)
       grind)
    | exact resolve eq28 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1763 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X2 (M.op X1 X1)) = (M.op (M.op X1 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X2 (M.op X1 X1)
       have i₂ := eq181 X1 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq28 X0 X1
       have i₂ := eq181 X0 X1 x
       grind)
    | exact superpose eq181 eq28
    | (have j0 := eq28 X2 (M.op X1 X1)
       grind)
    | (have r₁ := eq28 X0 (M.op (M.op X0 X0) x)
       have r₂ := eq181 X0 (M.op (M.op X0 X0) x) x
       grind)
    | (have r₁ := eq28 X0 (M.op X1 X1)
       have r₂ := eq181 X1 X1 (M.op X1 X1)
       grind)
    | exact resolve eq28 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1773 : ∀ X1 X2 : G, (k X2 (M.op X1 X1)) = (M.op (M.op X1 X1) X2) := by
    intro X1 X2
    first
    | (have j0 := eq1763 x X1 X2
       grind)
    | (have r₁ := eq1763 x X1 X2
       have r₂ := eq182 x X1
       grind)
    | (have r₁ := eq1763 X1 x X2
       have r₂ := eq182 x X1
       grind)
    | exact resolve eq1763 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1763
  have eq1787 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq182 X0 X1
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq182 X0 X1
       grind)
    | exact superpose eq182 eq11
    | (have j0 := eq11 (k X1 X1) X0
       grind)
    | exact resolve eq11 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1827 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq182 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq182
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq182 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1828 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq184 x
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq184
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq184 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq1881 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
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
  have eq1882 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq1884 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1885 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1884 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1884
  have eq1898 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1828 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828
  have eq1899 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1827 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1827
  have eq1914 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1787 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1787
  have eq1931 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq1898 X0
       have j1 := eq28 (k X0 X0) X0
       grind)
    | (have r₁ := eq1898 x
       have r₂ := eq28 X0 x
       grind)
    | exact resolve eq1898 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1898
  have eq2023 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X0 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 X1 X2 X0
       have i₂ := eq1773 X1 X0
       grind)
    | exact superpose eq1773 eq181
    | exact resolve eq181 eq1773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2025 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (k X0 (M.op X1 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq231 X2 X3 X1 X0
       have i₂ := eq1773 X1 X0
       grind)
    | exact superpose eq1773 eq231
    | exact resolve eq231 eq1773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq2041 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq214 sF4 x
       have i₂ := eq1773 sF4 sF3
       grind)
    | exact superpose eq1773 eq214
    | exact resolve eq214 eq1773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq2042 : ∀ X0 : G, (M.op X0 X0) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq179 X0 sF4
       have i₂ := eq1773 sF4 sF3
       grind)
    | exact superpose eq1773 eq179
    | exact resolve eq179 eq1773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq1773
  have eq2111 : ∀ X0 X1 X3 X4 : G, (k X0 (M.op X1 X1)) = (k X3 (M.op X4 X4)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq2023 X3 X4 x
       have i₂ := eq2023 X0 X1 x
       grind)
    | exact superpose eq2023 eq2023
    | exact resolve eq2023 eq2023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2194 : ∀ X0 X1 X2 : G, (k X1 (τ (M.op X2 X2))) = (τ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq456 X1 (M.op X2 X2)
       have i₂ := eq2023 (σ X1) X2 X0
       grind)
    | exact superpose eq2023 eq456
    | exact resolve eq456 eq2023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2438 : ∀ X0 : G, (k (τ (k X0 X0)) (τ X0)) = (M.op (τ X0) (τ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1931 (τ X0)
       have i₂ := eq483 X0 X0
       grind)
    | exact superpose eq483 eq1931
    | exact resolve eq1931 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2465 : ∀ X0 : G, (M.op (τ X0) (τ (k X0 X0))) = (τ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq2438 X0
       have i₂ := eq483 X0 (k X0 X0)
       grind)
    | exact superpose eq483 eq2438
    | exact resolve eq2438 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483 eq2438
  have eq6116 : ∀ X0 X3 : G, (τ (M.op X0 X0)) = (τ (M.op X3 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq2194 X3 x x
       have i₂ := eq2194 X0 x x
       grind)
    | exact superpose eq2194 eq2194
    | exact resolve eq2194 eq2194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6163 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X1 X1)) ∨ (τ (M.op X1 X1)) = (M.op (τ (M.op X1 X1)) (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1885 (τ (M.op X1 X1))
       have i₂ := eq2194 X0 (τ (M.op X1 X1)) X1
       grind)
    | exact superpose eq2194 eq1885
    | (have j0 := eq1885 (τ (M.op X1 X1))
       grind)
    | (have r₁ := eq1885 (τ (M.op X0 X0))
       have r₂ := eq2194 X0 (τ (M.op X0 X0)) X0
       grind)
    | exact resolve eq1885 eq2194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1885
  have eq6165 : ∀ X0 X1 X4 : G, (M.op X1 X1) = (M.op (τ (M.op X0 X0)) X4) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq1573 x (τ (M.op x x)) X1 X4
       have i₂ := eq2194 X0 (M.op x x) x
       grind)
    | exact superpose eq2194 eq1573
    | exact resolve eq1573 eq2194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6189 : ∀ X0 X1 : G, (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (τ (M.op X1 X1)) ∨ (τ (M.op X0 X0)) ≠ (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6163 X0 X1
       have i₂ := eq2042 (τ (M.op X1 X1))
       grind)
    | exact superpose eq2042 eq6163
    | (have j0 := eq6163 X0 X1
       grind)
    | exact resolve eq6163 eq2042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6163
  have eq6232 : ∀ X1 : G, (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (τ (M.op X1 X1)) := by
    intro X1
    first
    | (have j0 := eq6189 x X1
       grind)
    | (have r₁ := eq6189 x x
       have r₂ := eq6116 x x
       grind)
    | (have r₁ := eq6189 x x
       have r₂ := eq6116 x x
       grind)
    | exact resolve eq6189 eq6116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6116 eq6189
  have eq6902 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq6232 eq2023
    | exact resolve eq2023 eq6232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6905 : ∀ X0 X1 X2 : G, (k X1 (M.op X2 X2)) = (τ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq6232 eq2111
    | exact resolve eq2111 eq6232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2111 eq6232
  have eq7026 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6902 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq6902
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq6902 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7074 : ∀ X0 X1 X3 X4 : G, (M.op X1 X1) = (M.op (k (τ (M.op X0 X0)) X3) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq1573 x X3 X1 X4
       have i₂ := eq6902 X0 x
       grind)
    | exact superpose eq6902 eq1573
    | exact resolve eq1573 eq6902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7075 : ∀ X0 X2 X3 X4 : G, (τ (M.op X0 X0)) = (M.op (k (M.op X2 X2) X3) X4) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq1573 X2 X3 x X4
       have i₂ := eq6902 X0 x
       grind)
    | exact superpose eq6902 eq1573
    | exact resolve eq1573 eq6902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7143 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X1)
       have i₂ := eq6902 X1 X0
       grind)
    | exact superpose eq6902 eq14
    | exact resolve eq14 eq6902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7145 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq7026 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7026
  have eq7227 : ∀ X0 X2 : G, (σ (M.op X2 X2)) = (σ (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq7143 X0 x
       have i₂ := eq7143 X2 x
       grind)
    | exact superpose eq7143 eq7143
    | exact resolve eq7143 eq7143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7259 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (σ (M.op (k (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7143 x X3
       have i₂ := eq1573 X0 X1 x X2
       grind)
    | (have i₁ := eq7143 (k (M.op X0 X0) X1) X1
       have i₂ := eq1573 X0 X1 X2 (k (M.op X0 X0) X1)
       grind)
    | exact superpose eq1573 eq7143
    | exact resolve eq7143 eq1573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7273 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7143 x X1
       have i₂ := eq7143 X0 x
       grind)
    | exact superpose eq7143 eq7143
    | exact resolve eq7143 eq7143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7296 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X4)) X4) = (σ (M.op X0 X0)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq16 x X2 X3 X4
       have i₂ := eq7143 X0 x
       grind)
    | exact superpose eq7143 eq16
    | exact resolve eq16 eq7143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7318 : ∀ X0 X1 X3 X4 : G, (M.op X1 X1) = (M.op (k (σ (M.op X0 X0)) X3) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq1573 x X3 X1 X4
       have i₂ := eq7143 X0 x
       grind)
    | exact superpose eq7143 eq1573
    | exact resolve eq1573 eq7143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7324 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X2 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2023 X2 x X1
       have i₂ := eq7143 X0 x
       grind)
    | exact superpose eq7143 eq2023
    | exact resolve eq2023 eq7143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7351 : ∀ X0 X2 X3 : G, (σ (M.op X0 X0)) = (M.op (τ (M.op X2 X2)) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq6165 X2 x X3
       have i₂ := eq7143 X0 x
       grind)
    | exact superpose eq7143 eq6165
    | exact resolve eq6165 eq7143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6165
  have eq7354 : ∀ X0 X2 : G, (τ (M.op X2 X2)) = (σ (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq6902 X2 x
       have i₂ := eq7143 X0 x
       grind)
    | exact superpose eq7143 eq6902
    | exact resolve eq6902 eq7143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7367 : ∀ X0 X2 X3 : G, (k X2 (M.op X3 X3)) = (σ (M.op X0 X0)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq2025 X2 X3 x (M.op x x)
       have i₂ := eq7143 X0 (M.op x x)
       grind)
    | exact superpose eq7143 eq2025
    | exact resolve eq2025 eq7143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7872 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = (σ (k X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7227 (M.op x x) X2
       have i₂ := eq2025 X0 X1 x (M.op x x)
       grind)
    | exact superpose eq2025 eq7227
    | exact resolve eq7227 eq2025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2025
  have eq8150 : ∀ X0 X1 X3 : G, (τ (M.op X3 X3)) = (k X1 (τ (σ (σ (M.op X0 X0))))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq2194 X3 X1 x
       have i₂ := eq7273 X0 x
       grind)
    | exact superpose eq7273 eq2194
    | exact resolve eq2194 eq7273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2194
  have eq8215 : ∀ X0 X1 X3 : G, (τ (M.op X3 X3)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8150 X0 X1 X3
       have i₂ := eq15 (σ (M.op X0 X0))
       grind)
    | exact superpose eq15 eq8150
    | exact resolve eq8150 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8150
  have eq8545 : ∀ X0 X1 X3 : G, (τ (M.op X3 X3)) = (k X1 (σ (σ (M.op X0 X0)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq6905 X3 X1 x
       have i₂ := eq7273 X0 x
       grind)
    | exact superpose eq7273 eq6905
    | exact resolve eq6905 eq7273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6905
  have eq29548 : ∀ X0 X1 X2 : G, (σ (M.op X1 X1)) = (σ (k X2 (σ (σ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7872 X2 x X1
       have i₂ := eq7273 X0 x
       grind)
    | exact superpose eq7273 eq7872
    | exact resolve eq7872 eq7273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7273 eq7872
  have eq35262 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1881
       grind)
    | exact superpose eq1881 eq41
    | exact resolve eq41 eq1881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1881
  have eq35263 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq35262
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35262
    | exact resolve eq35262 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35262
  have eq35265 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq35263
    | exact resolve eq35263 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35263
  have eq44451 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (k X0 X0) X3) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq181 X2 X1 X3
       have i₂ := eq1914 X2 X0
       grind)
    | exact superpose eq1914 eq181
    | (have j1 := eq1914 X1 (M.op (k X0 X0) X3)
       grind)
    | exact resolve eq181 eq1914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq44454 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq182 X1 X2
       have i₂ := eq1914 X2 X0
       grind)
    | exact superpose eq1914 eq182
    | (have j1 := eq1914 X1 X0
       grind)
    | exact resolve eq182 eq1914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44488 : ∀ X0 X1 : G, (k X0 X0) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2042 X1
       have i₂ := eq1914 X1 X0
       grind)
    | exact superpose eq1914 eq2042
    | (have j1 := eq1914 X1 X0
       grind)
    | exact resolve eq2042 eq1914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44521 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (τ (k X0 X0)) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6902 X2 X1
       have i₂ := eq1914 X2 X0
       grind)
    | exact superpose eq1914 eq6902
    | (have j1 := eq1914 X1 (τ (k X0 X0))
       grind)
    | exact resolve eq6902 eq1914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6902
  have eq44703 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op (k (M.op X2 X2) X3) (k (M.op X2 X2) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1573 X2 X3 X1 (k (M.op X2 X2) X3)
       have i₂ := eq1914 (k (M.op X2 X2) X3) X0
       grind)
    | exact superpose eq1914 eq1573
    | (have j1 := eq1914 X1 X0
       grind)
    | exact resolve eq1573 eq1914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1573 eq1914
  have eq44768 : ∀ X0 X1 : G, (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = X0 ∨ (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq44703 X0 X1 x x
       have i₂ := eq2042 (k (M.op x x) x)
       grind)
    | exact superpose eq2042 eq44703
    | (have j0 := eq44703 X0 X1 x x
       grind)
    | exact resolve eq44703 eq2042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44703
  have eq57717 : ∀ X0 X1 X2 X3 : G, (σ (M.op X3 X3)) = (M.op (k (τ (M.op X0 X0)) X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7351 X3 x (τ (M.op x x))
       have i₂ := eq7074 X0 (τ (M.op x x)) X1 X2
       grind)
    | exact superpose eq7074 eq7351
    | exact resolve eq7351 eq7074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7074 eq7351
  have eq70157 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) = (M.op (σ (k (M.op X0 X0) X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7318 X0 X2 (σ X1) X3
       have i₂ := eq10 (M.op X0 X0) X1
       grind)
    | exact superpose eq10 eq7318
    | exact resolve eq7318 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7318
  have eq137565 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (σ (M.op (σ (k (M.op X0 X0) X1)) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7259 x x (k (M.op x x) x) X3
       have i₂ := eq70157 X0 X1 (k (M.op x x) x) X2
       grind)
    | exact superpose eq70157 eq7259
    | exact resolve eq7259 eq70157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7259
  have eq137566 : ∀ X0 X1 X2 X3 : G, (τ (M.op X3 X3)) = (M.op (σ (k (M.op X0 X0) X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7075 X3 x x (k (M.op x x) x)
       have i₂ := eq70157 X0 X1 (k (M.op x x) x) X2
       grind)
    | exact superpose eq70157 eq7075
    | exact resolve eq7075 eq70157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7075 eq70157
  have eq338370 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (k y y) (τ (k (σ y) (σ y)))) ∨ (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq586 (k sF3 sF3)
       have i₂ := eq1899 (k sF3 sF3) x
       grind)
    | exact superpose eq1899 eq586
    | (have j1 := eq1899 (σ y) (k (σ y) (σ y))
       grind)
    | exact resolve eq586 eq1899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338493 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (k y y) (k y y)) ∨ (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq116 eq338370
    | exact resolve eq338370 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338370
  have eq338518 : ∀ X0 : G, (k (σ y) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (τ (M.op X0 X0)) = (k (k y y) (k y y)) := by
    intro X0
    first
    | (have i₁ := eq338493 X0
       have i₂ := eq2042 (k sF3 sF3)
       grind)
    | exact superpose eq2042 eq338493
    | (have j0 := eq338493 X0
       grind)
    | exact resolve eq338493 eq2042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338493
  have eq338523 : (k (σ y) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (τ (σ y)) = (k (k y y) (k y y)) := by
    first
    | exact superpose eq44488 eq338518
    | (have j1 := eq44488 (σ y) x
       grind)
    | exact resolve eq338518 eq44488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338518
  have eq338524 : y = (k (k y y) (k y y)) ∨ (k (σ y) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq32 eq338523
    | exact resolve eq338523 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338523
  have eq482120 : ∀ X0 : G, (M.op X0 X0) = (k (k y y) (τ (k (σ y) (σ y)))) ∨ (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq586 (k sF3 sF3)
       have i₂ := eq7145 (k sF3 sF3) x
       grind)
    | exact superpose eq7145 eq586
    | (have j1 := eq7145 (k (σ y) (σ y)) x
       grind)
    | exact resolve eq586 eq7145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586 eq7145
  have eq482145 : ∀ X0 : G, (M.op X0 X0) = (k (k y y) (k y y)) ∨ (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq116 eq482120
    | exact resolve eq482120 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482120
  have eq482750 : ∀ X0 : G, (k (σ y) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op X0 X0) = (k (k y y) (k y y)) := by
    intro X0
    first
    | (have i₁ := eq482145 X0
       have i₂ := eq2042 (k sF3 sF3)
       grind)
    | exact superpose eq2042 eq482145
    | (have j0 := eq482145 X0
       grind)
    | exact resolve eq482145 eq2042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2042 eq482145
  have eq482959 : ∀ X0 : G, (k (σ y) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | exact superpose eq338524 eq482750
    | exact resolve eq482750 eq338524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338524 eq482750
  have eq483038 : (k (σ y) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (σ y) := by
    first
    | exact superpose eq44488 eq482959
    | (have j1 := eq44488 (σ y) x
       grind)
    | exact resolve eq482959 eq44488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44488 eq482959
  have eq487334 : ∀ X0 : G, (M.op X0 X0) = (k (σ y) (σ y)) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq483038 eq2023
    | exact resolve eq2023 eq483038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2023 eq483038
  have eq534659 : ∀ X0 X1 : G, (τ (k X1 X1)) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq44521 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44521
  have eq1227586 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) X2) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq44451 X1 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44451
  have eq1230227 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1227586 X2 X1 (k X1 X1)
       have i₂ := eq182 (k X1 X1) X0
       grind)
    | (have i₁ := eq1227586 X2 X1 (k X1 X1)
       have i₂ := eq182 X0 (k X1 X1)
       grind)
    | exact superpose eq182 eq1227586
    | (have j0 := eq1227586 X2 X1 X2
       grind)
    | (have r₁ := eq1227586 X0 (M.op X1 X1) (k (M.op X1 X1) (M.op X1 X1))
       have r₂ := eq182 (k (M.op X1 X1) (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq1227586 X0 (M.op X0 X0) (k (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq182 X0 (k (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq1227586 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227586
  have eq1321318 : ∀ X0 X1 X2 : G, (σ (M.op X1 X1)) = X0 ∨ (M.op X2 X2) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7367 X0 X2 x
       have i₂ := eq44768 (k X2 (M.op x x)) X1
       grind)
    | exact superpose eq44768 eq7367
    | (have j1 := eq44768 X0 X2
       grind)
    | exact resolve eq7367 eq44768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7367 eq44768
  have eq1324575 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq35265 eq1882
    | exact resolve eq1882 eq35265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1882 eq35265
  have eq1324584 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1324575
       have r₂ := eq27
       grind)
    | exact resolve eq1324575 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324575
  have eq1324591 : (σ y) = (k y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1899 eq1324584
    | (have j1 := eq1899 y x
       grind)
    | exact resolve eq1324584 eq1899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1899 eq1324584
  have eq1324596 : (σ y) = (k y y) ∨ (σ x) = (k x x) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq44454 eq1324591
    | (have j1 := eq44454 y x y
       grind)
    | exact resolve eq1324591 eq44454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324591
  have eq1326790 : ∀ X0 : G, y ≠ (τ (σ y)) ∨ (M.op X0 X0) = y ∨ (σ x) = (k x x) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq534659 X0 y
       have i₂ := eq1324596
       grind)
    | exact superpose eq1324596 eq534659
    | (have j0 := eq534659 X0 y
       grind)
    | exact resolve eq534659 eq1324596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324596
  have eq1326815 : y ≠ (τ (σ y)) ∨ (σ x) = (k x x) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have j0 := eq1326790 y
       have j1 := eq1230227 x y y
       grind)
    | (have r₁ := eq1326790 x
       have r₂ := eq1230227 x y x
       grind)
    | (have r₁ := eq1326790 x
       have r₂ := eq1230227 y y x
       grind)
    | (have r₁ := eq1326790 x
       have r₂ := eq1230227 y x x
       grind)
    | exact resolve eq1326790 eq1230227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326790
  have eq1326868 : (σ x) = (k x x) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1326815
       have r₂ := eq32
       grind)
    | exact resolve eq1326815 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326815
  have eq1326952 : ∀ X0 : G, x ≠ (τ (σ x)) ∨ (M.op X0 X0) = x ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq534659 X0 x
       have i₂ := eq1326868
       grind)
    | exact superpose eq1326868 eq534659
    | (have j0 := eq534659 X0 x
       grind)
    | exact resolve eq534659 eq1326868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534659 eq1326868
  have eq1326972 : x ≠ (τ (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have j0 := eq1326952 y
       have j1 := eq1230227 x y y
       grind)
    | (have r₁ := eq1326952 x
       have r₂ := eq1230227 x x x
       grind)
    | (have r₁ := eq1326952 x
       have r₂ := eq1230227 y y x
       grind)
    | (have r₁ := eq1326952 x
       have r₂ := eq1230227 y x x
       grind)
    | exact resolve eq1326952 eq1230227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230227 eq1326952
  have eq1327012 : y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1326972
       have r₂ := eq30
       grind)
    | exact resolve eq1326972 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326972
  have eq1327043 : ∀ X0 : G, (M.op X0 X0) = y ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq1327012
       have i₂ := eq182 y x
       grind)
    | (have i₁ := eq1327012
       have i₂ := eq182 X0 y
       grind)
    | exact superpose eq182 eq1327012
    | exact resolve eq1327012 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1327066 : ∀ X0 : G, x = (M.op y y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq182 X0 y
       have i₂ := eq1327012
       grind)
    | exact superpose eq1327012 eq182
    | exact resolve eq182 eq1327012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1327373 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (σ (σ y))) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq8545 y X1 X0
       have i₂ := eq1327012
       grind)
    | exact superpose eq1327012 eq8545
    | exact resolve eq8545 eq1327012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8545
  have eq1327451 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (k X1 (σ (σ y)))) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq29548 y X0 X1
       have i₂ := eq1327012
       grind)
    | exact superpose eq1327012 eq29548
    | exact resolve eq29548 eq1327012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29548
  have eq1327515 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (M.op (σ (k y X1)) X2)) ∨ x = (M.op y y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq137565 y X1 X2 X0
       have i₂ := eq1327012
       grind)
    | exact superpose eq1327012 eq137565
    | exact resolve eq137565 eq1327012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137565
  have eq1327516 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) = (M.op (σ (k y X1)) X2) ∨ x = (M.op y y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq137566 y X1 X2 X0
       have i₂ := eq1327012
       grind)
    | exact superpose eq1327012 eq137566
    | exact resolve eq137566 eq1327012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137566 eq1327012
  have eq1327759 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) = (M.op (k (σ y) (σ X1)) X2) ∨ x = (M.op y y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1327516 X0 X1 X2
       have i₂ := eq37 X1
       grind)
    | exact superpose eq37 eq1327516
    | exact resolve eq1327516 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327516
  have eq1327760 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (M.op (k (σ y) (σ X1)) X2)) ∨ x = (M.op y y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1327515 X0 X1 X2
       have i₂ := eq37 X1
       grind)
    | exact superpose eq37 eq1327515
    | exact resolve eq1327515 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq1327515
  have eq1327816 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (k X1 (σ (σ y)))) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq1327451 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1327451
    | (have j0 := eq1327451 X0 X1
       grind)
    | exact resolve eq1327451 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327451
  have eq1327894 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (σ (σ y))) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq1327373 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1327373
    | (have j0 := eq1327373 X0 X1
       grind)
    | exact resolve eq1327373 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327373
  have eq1328256 : ∀ X1 X2 : G, (τ y) = (M.op (k (σ y) (σ X1)) X2) ∨ x = (M.op y y) := by
    intro X1 X2
    first
    | exact superpose eq1327066 eq1327759
    | exact resolve eq1327759 eq1327066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327759
  have eq1328257 : ∀ X1 X2 : G, (k x x) = (σ (M.op (k (σ y) (σ X1)) X2)) ∨ x = (M.op y y) := by
    intro X1 X2
    first
    | exact superpose eq44454 eq1327760
    | (have j1 := eq44454 x X1 y
       grind)
    | exact resolve eq1327760 eq44454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327760
  have eq1328298 : ∀ X1 : G, (σ y) = (σ (k X1 (σ (σ y)))) ∨ x = (M.op y y) := by
    intro X1
    first
    | exact superpose eq1327066 eq1327816
    | exact resolve eq1327816 eq1327066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327816
  have eq1328374 : ∀ X1 : G, (τ y) = (k X1 (σ (σ y))) ∨ x = (M.op y y) := by
    intro X1
    first
    | exact superpose eq1327066 eq1327894
    | exact resolve eq1327894 eq1327066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327066 eq1327894
  have eq1328618 : (k x x) = (σ (τ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1328256 eq1328257
    | exact resolve eq1328257 eq1328256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328256 eq1328257
  have eq1328630 : ∀ X1 : G, (σ y) = (σ (k X1 (σ (σ y)))) ∨ x = (M.op y y) := by
    intro X1
    first
    | (have i₁ := eq1328298 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1328298
    | (have j0 := eq1328298 X1
       grind)
    | exact resolve eq1328298 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328298
  have eq1328857 : y = (k x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1328618
       have i₂ := eq14 y
       grind)
    | exact superpose eq14 eq1328618
    | exact resolve eq1328618 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328618
  have eq1328866 : (σ y) = (σ (τ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1328374 eq1328630
    | exact resolve eq1328630 eq1328374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328374 eq1328630
  have eq1329013 : x = (M.op y y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq1328866
       have i₂ := eq14 y
       grind)
    | exact superpose eq14 eq1328866
    | exact resolve eq1328866 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328866
  have eq1329214 : ∀ X0 : G, (M.op X0 X0) = x ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq182 X0 y
       have i₂ := eq1329013
       grind)
    | exact superpose eq1329013 eq182
    | exact resolve eq182 eq1329013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq1329408 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq7143 y X0
       have i₂ := eq1329013
       grind)
    | exact superpose eq1329013 eq7143
    | exact resolve eq7143 eq1329013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7143
  have eq1329420 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ x)) ∨ y = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq7324 y X0 X1
       have i₂ := eq1329013
       grind)
    | exact superpose eq1329013 eq7324
    | exact resolve eq7324 eq1329013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7324
  have eq1329433 : ∀ X0 : G, (σ x) = (τ (M.op X0 X0)) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq7354 y X0
       have i₂ := eq1329013
       grind)
    | exact superpose eq1329013 eq7354
    | exact resolve eq7354 eq1329013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7354
  have eq1329510 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (σ x)) ∨ y = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq8215 y X1 X0
       have i₂ := eq1329013
       grind)
    | exact superpose eq1329013 eq8215
    | exact resolve eq8215 eq1329013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8215 eq1329013
  have eq1330054 : ∀ X0 X1 : G, (k X1 (σ x)) = (τ (M.op X0 X0)) ∨ y = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq1329510 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1329510
    | (have j0 := eq1329510 X0 X1
       grind)
    | exact resolve eq1329510 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329510
  have eq1330131 : ∀ X0 : G, (σ x) = (τ (M.op X0 X0)) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1329433 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1329433
    | (have j0 := eq1329433 X0
       grind)
    | exact resolve eq1329433 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329433
  have eq1330144 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ x)) ∨ y = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq1329420 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1329420
    | (have j0 := eq1329420 X0 X1
       grind)
    | exact resolve eq1329420 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329420
  have eq1330155 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1329408 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1329408
    | (have j0 := eq1329408 X0
       grind)
    | exact resolve eq1329408 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329408
  have eq1330538 : ∀ X1 : G, (τ (k (σ y) (σ y))) = (k X1 (σ x)) ∨ y = (σ y) := by
    intro X1
    first
    | exact superpose eq487334 eq1330054
    | exact resolve eq1330054 eq487334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1330054
  have eq1330612 : (σ x) = (τ (k (σ y) (σ y))) ∨ y = (σ y) := by
    first
    | exact superpose eq487334 eq1330131
    | exact resolve eq1330131 eq487334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487334 eq1330131
  have eq1330625 : ∀ X1 : G, x = (k X1 (σ x)) ∨ y = (σ y) := by
    intro X1
    first
    | exact superpose eq1329214 eq1330144
    | exact resolve eq1330144 eq1329214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1330144
  have eq1330962 : ∀ X1 : G, (k y y) = (k X1 (σ x)) ∨ y = (σ y) := by
    intro X1
    first
    | exact superpose eq116 eq1330538
    | exact resolve eq1330538 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1330538
  have eq1331014 : (σ x) = (k y y) ∨ y = (σ y) := by
    first
    | exact superpose eq116 eq1330612
    | exact resolve eq1330612 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq1330612
  have eq1331317 : x = (k y y) ∨ y = (σ y) := by
    first
    | exact superpose eq1330625 eq1330962
    | exact resolve eq1330962 eq1330625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1330962
  have eq1331576 : y = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq1331014 eq1331317
    | exact resolve eq1331317 eq1331014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1331014 eq1331317
  have eq1334154 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq178 X0 sF0
       have i₂ := eq1329214 sF0
       grind)
    | exact superpose eq1329214 eq178
    | exact resolve eq178 eq1329214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1334244 : ∀ X0 X1 X2 : G, x = (M.op (M.op X0 (M.op X1 X2)) X2) ∨ y = (σ y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq666 x x (M.op x (M.op x x)) X0 X1 X2
       have i₂ := eq1329214 (M.op x (M.op x x))
       grind)
    | exact superpose eq1329214 eq666
    | exact resolve eq666 eq1329214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666 eq1329214
  have eq1334587 : ∀ X0 X1 X2 : G, (σ x) = (M.op (M.op X0 (M.op X1 X2)) X2) ∨ y = (σ y) := by
    intro X0 X1 X2
    first
    | exact superpose eq1331576 eq1334244
    | exact resolve eq1334244 eq1331576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334244
  have eq1334665 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1334154 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1334154
    | (have j0 := eq1334154 X0
       grind)
    | exact resolve eq1334154 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334154
  have eq1343730 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq2041 sF4
       have i₂ := eq1330155 sF4
       grind)
    | exact superpose eq1330155 eq2041
    | exact resolve eq2041 eq1330155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2041 eq1330155
  have eq1344170 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (σ y) := by
    first
    | exact superpose eq26 eq1343730
    | exact resolve eq1343730 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1343730
  have eq1345537 : x = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq1330625 eq1344170
    | exact resolve eq1344170 eq1330625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1330625 eq1344170
  have eq1346826 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq1331576 eq1345537
    | exact resolve eq1345537 eq1331576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1331576 eq1345537
  have eq1351505 : (σ (M.op x y)) ≠ (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq1346826 eq27
    | exact resolve eq27 eq1346826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346826
  have eq1358430 : ∀ X0 X1 X2 : G, (σ (M.op x y)) = (M.op (M.op X0 (M.op X1 X2)) X2) ∨ y = (σ y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7296 x X0 X1 X2
       have i₂ := eq1334665 x
       grind)
    | exact superpose eq1334665 eq7296
    | exact resolve eq7296 eq1334665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7296 eq1334665
  have eq1360270 : ∀ X0 X1 X2 : G, (σ (M.op x y)) = (M.op (M.op X0 (M.op X1 X2)) X2) ∨ y = (σ y) := by
    intro X0 X1 X2
    first
    | exact superpose eq20 eq1358430
    | (have j0 := eq1358430 X0 X1 X2
       grind)
    | exact resolve eq1358430 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358430
  have eq1361639 : (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq1334587 eq1360270
    | exact resolve eq1360270 eq1334587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334587 eq1360270
  have eq1362966 : y = (σ y) := by
    first
    | (have r₁ := eq1361639
       have r₂ := eq1351505
       grind)
    | exact resolve eq1361639 eq1351505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1351505 eq1361639
  have eq1364224 : (M.op x y) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1362966
       grind)
    | exact superpose eq1362966 eq18
    | exact resolve eq18 eq1362966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1364225 : (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1362966
       grind)
    | exact superpose eq1362966 eq24
    | exact resolve eq24 eq1362966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1364444 : ∀ X0 : G, (τ (k (σ y) X0)) = (k (σ y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq1364225 eq456
    | exact resolve eq456 eq1364225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq1392199 : ∀ X0 : G, y = (σ (M.op X0 X0)) ∨ x = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1327043 (k (τ (M.op X0 X0)) x)
       have i₂ := eq57717 X0 x (k (τ (M.op X0 X0)) x) x
       grind)
    | exact superpose eq57717 eq1327043
    | exact resolve eq1327043 eq57717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57717
  have eq1392565 : ∀ X0 X1 : G, (σ y) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = x := by
    intro X0 X1
    first
    | (have i₁ := eq7227 X1 X0
       have i₂ := eq1327043 X0
       grind)
    | exact superpose eq1327043 eq7227
    | (have j1 := eq1327043 X0
       grind)
    | exact resolve eq7227 eq1327043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7227 eq1327043
  have eq1394500 : ∀ X0 X1 : G, (σ y) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = x := by
    intro X0 X1
    first
    | (have i₁ := eq1392565 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1392565
    | (have j0 := eq1392565 X0 X1
       grind)
    | exact resolve eq1392565 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1392565
  have eq1394832 : ∀ X0 : G, (σ y) = (σ (M.op X0 X0)) ∨ x = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1392199 X0
       have i₂ := eq1362966
       grind)
    | exact superpose eq1362966 eq1392199
    | (have j0 := eq1392199 X0
       grind)
    | exact resolve eq1392199 eq1362966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392199
  have eq1395943 : ∀ X0 : G, (σ y) = (σ (k x x)) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq44454 eq1394500
    | (have j0 := eq1394500 X0 x
       have j1 := eq44454 x x X0
       grind)
    | exact resolve eq1394500 eq44454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44454 eq1394500
  have eq1396247 : ∀ X0 : G, (σ y) = (σ (k x x)) ∨ x = (σ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq1321318 eq1394832
    | (have j0 := eq1394832 X0
       have j1 := eq1321318 x X0 x
       grind)
    | exact resolve eq1394832 eq1321318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321318 eq1394832
  have eq1397206 : ∀ X0 : G, (σ y) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq1395943 X0
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq1395943
    | (have j0 := eq1395943 X0
       grind)
    | exact resolve eq1395943 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395943
  have eq1397469 : ∀ X0 : G, (σ y) = (k (σ x) (σ x)) ∨ x = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1396247 X0
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq1396247
    | (have j0 := eq1396247 X0
       grind)
    | exact resolve eq1396247 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396247
  have eq1398122 : ∀ X0 : G, (σ y) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq1397206 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1397206
    | (have j0 := eq1397206 X0
       grind)
    | exact resolve eq1397206 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397206
  have eq1398304 : ∀ X0 : G, (σ y) = (k (σ x) (σ x)) ∨ x = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1397469 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1397469
    | (have j0 := eq1397469 X0
       grind)
    | exact resolve eq1397469 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397469
  have eq1398837 : (σ y) = (k (σ x) (σ x)) ∨ x = (σ x) := by
    first
    | exact superpose eq1398122 eq1398304
    | exact resolve eq1398304 eq1398122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398122 eq1398304
  have eq1399124 : (σ y) = (k (σ x) (σ x)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq1398837
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1398837
    | exact resolve eq1398837 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1398837
  have eq1399473 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (σ x) := by
    first
    | exact superpose eq1399124 eq1931
    | exact resolve eq1931 eq1399124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1399478 : (τ (k (σ y) (σ x))) = (M.op (τ (σ x)) (τ (σ y))) ∨ x = (σ x) := by
    first
    | exact superpose eq1399124 eq2465
    | exact resolve eq2465 eq1399124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2465 eq1399124
  have eq1399540 : (τ (k (σ y) (σ x))) = (M.op (τ (σ x)) y) ∨ x = (σ x) := by
    first
    | exact superpose eq32 eq1399478
    | exact resolve eq1399478 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1399478
  have eq1399542 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (σ x) := by
    first
    | exact superpose eq26 eq1399473
    | exact resolve eq1399473 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399473
  have eq1399567 : (τ (k (σ y) (σ x))) = (M.op (τ (σ x)) (σ y)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq1399540
       have i₂ := eq1362966
       grind)
    | exact superpose eq1362966 eq1399540
    | exact resolve eq1399540 eq1362966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399540
  have eq1399583 : (τ (k (σ y) (σ x))) = (M.op x (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq30 eq1399567
    | exact resolve eq1399567 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399567
  have eq1399594 : (M.op x y) = (τ (k (σ y) (σ x))) ∨ x = (σ x) := by
    first
    | exact superpose eq1364224 eq1399583
    | exact resolve eq1399583 eq1364224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399583
  have eq1399597 : (M.op x y) = (k y x) ∨ x = (σ x) := by
    first
    | exact superpose eq115 eq1399594
    | exact resolve eq1399594 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq1399594
  have eq1399599 : (M.op x y) = (k (σ y) x) ∨ x = (σ x) := by
    first
    | (have i₁ := eq1399597
       have i₂ := eq1362966
       grind)
    | exact superpose eq1362966 eq1399597
    | exact resolve eq1399597 eq1362966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399597
  have eq1403374 : (τ (M.op (σ x) (σ y))) = (k (σ y) (τ (σ x))) ∨ x = (σ x) := by
    first
    | exact superpose eq1399542 eq1364444
    | exact resolve eq1364444 eq1399542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1364444 eq1399542
  have eq1403384 : (τ (M.op (σ x) (σ y))) = (k (σ y) x) ∨ x = (σ x) := by
    first
    | exact superpose eq30 eq1403374
    | exact resolve eq1403374 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1403374
  have eq1403390 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (σ x) := by
    first
    | exact superpose eq1399599 eq1403384
    | exact resolve eq1403384 eq1399599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399599 eq1403384
  have eq1403398 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq1403390 eq14
    | exact resolve eq14 eq1403390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1403390
  have eq1403452 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq20 eq1403398
    | exact resolve eq1403398 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1403398
  have eq1403459 : x = (σ x) := by
    first
    | (have r₁ := eq1403452
       have r₂ := eq27
       grind)
    | exact resolve eq1403452 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1403452
  have eq1403469 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq1403459
       grind)
    | exact superpose eq1403459 eq40
    | exact resolve eq40 eq1403459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq1403517 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1364224
       have i₂ := eq1403459
       grind)
    | exact superpose eq1403459 eq1364224
    | exact resolve eq1364224 eq1403459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1364224
  have eq1403904 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1403517 eq26
    | exact resolve eq26 eq1403517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1403517
  have eq1403971 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq1403904 eq27
    | exact resolve eq27 eq1403904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq1463454 : (M.op x y) = (k y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1931 x
       have i₂ := eq1328857
       grind)
    | exact superpose eq1328857 eq1931
    | exact resolve eq1931 eq1328857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1931 eq1328857
  have eq1463516 : (M.op x y) = (k y x) := by
    first
    | (have j1 := eq1753 x x y
       grind)
    | (have r₁ := eq1463454
       have r₂ := eq1753 y x x
       grind)
    | exact resolve eq1463454 eq1753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753 eq1463454
  have eq1463541 : (M.op (σ x) y) = (k y (σ x)) := by
    first
    | (have i₁ := eq1463516
       have i₂ := eq1403459
       grind)
    | exact superpose eq1403459 eq1463516
    | exact resolve eq1463516 eq1403459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1403459 eq1463516
  have eq1463555 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1463541
       have i₂ := eq1362966
       grind)
    | exact superpose eq1362966 eq1463541
    | exact resolve eq1463541 eq1362966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1362966 eq1463541
  have eq1463565 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq1463555
    | exact resolve eq1463555 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1463555
  have eq1463574 : (M.op x y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1403904 eq1463565
    | exact resolve eq1463565 eq1403904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1403904 eq1463565
  have eq1463599 : (σ (M.op x y)) = (k (σ (σ y)) (σ x)) := by
    first
    | exact superpose eq1463574 eq1403469
    | exact resolve eq1403469 eq1463574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1403469
  have eq1463605 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1364225 eq1463599
    | exact resolve eq1463599 eq1364225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1364225 eq1463599
  have eq1463614 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1463574 eq1463605
    | exact resolve eq1463605 eq1463574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1463574 eq1463605
  have eq1463632 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1463614 eq20
    | exact resolve eq20 eq1463614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1463614
  have eq1463790 : False := by grind
  exact eq1463790

/-- `Equation3926`: `x ◇ y = (x ◇ (y ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,Y) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxy_pyy_pxy_y_pxy_Equation3926 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3926 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3926.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq41 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 (M.op X0 X1)) X2) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 (M.op X0 X1)) X2) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq41 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq41 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq41 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1 x
       have i₂ := eq9 X1 X0 x
       grind)
    | exact superpose eq9 eq51
    | (have j0 := eq51 X0 X1 x
       grind)
    | exact resolve eq51 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq71 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq63 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq63 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq63 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq71 (σ X0) (σ X1)
       grind)
    | exact superpose eq71 eq15
    | exact resolve eq15 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 X1
       have i₂ := eq71 X0 X1
       grind)
    | exact superpose eq71 eq74
    | exact resolve eq74 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq74
  have eq77 : False := by grind
  exact eq77

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pxy_pyx_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq2634 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2667 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2634 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2634
  have eq2668 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2667 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2667
  have eq2697 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq2668 X1 X0
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq2668 X0 X1
       grind)
    | exact superpose eq2668 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq2668 X1 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq2668 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq2668 X1 X1
       grind)
    | exact resolve eq12 eq2668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2698 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq2668 X0 X1
       grind)
    | (have i₁ := eq13 X1 X0
       have i₂ := eq2668 X0 X1
       grind)
    | exact superpose eq2668 eq13
    | (have j1 := eq2668 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq2668 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq2668 X0 X1
       grind)
    | exact resolve eq13 eq2668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2668
  have eq2705 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2698 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2698
  have eq2706 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2705 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2705
  have eq2707 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2697 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2697
  have eq2711 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2707 X0 X1
       have j1 := eq2706 X0 X1
       grind)
    | (have r₁ := eq2707 X0 X1
       have r₂ := eq2706 X0 X1
       grind)
    | (have r₁ := eq2707 X1 X1
       have r₂ := eq2706 X1 X1
       grind)
    | exact resolve eq2707 eq2706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2706 eq2707
  have eq2754 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq2711 (σ X0) (σ X1)
       grind)
    | exact superpose eq2711 eq15
    | exact resolve eq15 eq2711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2873 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2754 X0 X1
       have i₂ := eq2711 X0 X1
       grind)
    | exact superpose eq2711 eq2754
    | exact resolve eq2754 eq2711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2711 eq2754
  have eq3940 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2873 x y
       grind)
    | exact superpose eq2873 eq16
    | (have r₁ := eq16
       have r₂ := eq2873 x y
       grind)
    | exact resolve eq16 eq2873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2873
  have eq3957 : False := by grind
  exact eq3957

/-- `Equation432`: `x = x ◇ (y ◇ (x ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_y_pxy_pyx_Equation432 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law432 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law432.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X0)))) = X0 := by
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
  have eq50 : x ≠ (M.op x y) ∨ y = (k x y) := by
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
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op y (M.op x y)))) := by
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
  have eq57 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X0) X0 X0
       have i₂ := eq14 X0 (M.op X1 X0) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq87 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq87
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq87
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq87
       grind)
    | exact superpose eq87 eq16
    | exact resolve eq16 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq92
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq92
    | exact resolve eq92 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq98
    | exact resolve eq98 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq99
    | exact resolve eq99 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
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
  have eq147 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq130 eq16
    | exact resolve eq16 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq131 eq16
    | exact resolve eq16 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq213 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq221 : (M.op x y) ≠ (M.op x y) ∨ y = (k (M.op x y) y) := by
    first
    | exact superpose eq213 eq13
    | (have j0 := eq13 (M.op x y) y
       grind)
    | (have r₁ := eq13 (M.op x y) y
       have r₂ := eq213
       grind)
    | exact resolve eq13 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq222 : y = (k (M.op x y) y) := by grind
  clear eq221
  have eq225 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq222 eq130
    | exact resolve eq130 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq229 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq225
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq225
    | exact resolve eq225 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq232 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq229 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq11 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq232
  have eq236 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq244 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq236 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) (σ y)
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ y)
       have r₂ := eq236
       grind)
    | exact resolve eq13 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq245 : (σ y) = (k (M.op (σ x) (σ y)) (σ y)) := by grind
  clear eq244
  have eq259 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X1 (M.op X0 X1)) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X1)
       have i₂ := eq59 X1 X0
       grind)
    | exact superpose eq59 eq12
    | (have j0 := eq12 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X0)
       have r₂ := eq59 X0 X1
       grind)
    | exact resolve eq12 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X1
       have i₂ := eq59 X1 X0
       grind)
    | exact superpose eq59 eq13
    | (have j0 := eq13 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq13 (M.op X1 X0) X0
       have r₂ := eq59 X0 X1
       grind)
    | exact resolve eq13 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq261 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq266 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k X1 (M.op X0 X1)) ∨ (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq259 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq710 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq68 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq711 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq68 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq712 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq711 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq883 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq233 eq12
    | (have j0 := eq12 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) (σ y)
       have r₂ := eq233
       grind)
    | (have r₁ := eq12 (σ y) (σ (M.op x y))
       have r₂ := eq233
       grind)
    | exact resolve eq12 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq891 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq883
  have eq892 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq891
  have eq893 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq229 eq892
    | exact resolve eq892 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229 eq892
  have eq926 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq893 eq59
    | exact resolve eq59 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq3588 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq712 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq712
    | (have j0 := eq712 (τ X0)
       grind)
    | exact resolve eq712 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq712
  have eq3597 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3588 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3588
    | (have j0 := eq3588 X0
       grind)
    | exact resolve eq3588 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3588
  have eq3603 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3597 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3597
    | (have j0 := eq3597 X0
       grind)
    | exact resolve eq3597 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3597
  have eq12764 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq100 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq12771 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq12764
    | exact resolve eq12764 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12764
  have eq12782 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq12771
       have r₂ := eq27
       grind)
    | exact resolve eq12771 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12771
  have eq12785 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq12782
    | exact resolve eq12782 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12782
  have eq12794 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq12785 eq265
    | exact resolve eq265 eq12785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq12785
  have eq12907 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq12794 eq97
    | exact resolve eq97 eq12794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq12794
  have eq12936 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq28 eq12907
    | exact resolve eq12907 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq12907
  have eq12939 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq12936
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq12936
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq12936
       have r₂ := eq13 y x
       grind)
    | exact resolve eq12936 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12936
  have eq12948 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq12939
       grind)
    | exact superpose eq12939 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq12939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12952 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq710 x y
       have i₂ := eq12939
       grind)
    | exact superpose eq12939 eq710
    | (have j0 := eq710 x y
       grind)
    | exact resolve eq710 eq12939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12939
  have eq12957 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12952
  have eq12959 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12948
  have eq12963 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12957
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12957
    | exact resolve eq12957 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12957
  have eq12967 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12959
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12959
    | exact resolve eq12959 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12959
  have eq12968 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12967
  have eq12980 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12963
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12963
    | exact resolve eq12963 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12963
  have eq12986 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq12980
    | exact resolve eq12980 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12980
  have eq12987 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq12986
  have eq12994 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12987
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12987
    | exact resolve eq12987 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12987
  have eq12999 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12994
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12994
    | exact resolve eq12994 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12994
  have eq13017 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq266 y x
       have i₂ := eq12968
       grind)
    | exact superpose eq12968 eq266
    | exact resolve eq266 eq12968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12968
  have eq13026 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13017
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13017
    | exact resolve eq13017 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13017
  have eq13033 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13026
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13026
    | exact resolve eq13026 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13026
  have eq13034 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13033
  have eq13225 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12999 eq266
    | exact resolve eq266 eq12999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12999
  have eq13234 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq13225
    | exact resolve eq13225 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13225
  have eq13241 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq13234
    | exact resolve eq13234 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13234
  have eq13242 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13241
  have eq13246 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq13034
       grind)
    | exact superpose eq13034 eq44
    | exact resolve eq44 eq13034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq13034
  have eq13272 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq13246
    | exact resolve eq13246 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13246
  have eq14297 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13272 eq13242
    | exact resolve eq13242 eq13272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13242 eq13272
  have eq14306 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14297
  have eq14308 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14306
       have r₂ := eq27
       grind)
    | exact resolve eq14306 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14306
  have eq14328 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14308 eq245
    | exact resolve eq245 eq14308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq14308
  have eq14356 : (τ (σ y)) = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14328 eq55
    | exact resolve eq55 eq14328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq14328
  have eq14390 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq14356
    | exact resolve eq14356 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq14356
  have eq14395 : y = (k x y) := by
    first
    | (have r₁ := eq14390
       have r₂ := eq50
       grind)
    | exact resolve eq14390 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq14390
  have eq14406 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq14395
       grind)
    | exact superpose eq14395 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq14395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14410 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq710 y x
       have i₂ := eq14395
       grind)
    | exact superpose eq14395 eq710
    | (have j0 := eq710 y x
       grind)
    | exact resolve eq710 eq14395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq14416 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14410
  have eq14418 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq14406
  have eq14423 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14416
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14416
    | exact resolve eq14416 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14416
  have eq14427 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14418
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14418
    | exact resolve eq14418 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14418
  have eq14439 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14423
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14423
    | exact resolve eq14423 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14423
  have eq14447 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq14439
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14439
    | exact resolve eq14439 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14439
  have eq14454 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq14447
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14447
    | exact resolve eq14447 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14447
  have eq14461 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq14454
    | exact resolve eq14454 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14454
  have eq15618 : ∀ X0 : G, x = (M.op x (M.op X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq14427
       grind)
    | exact superpose eq14427 eq14
    | exact resolve eq14 eq14427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15624 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq266 y x
       have i₂ := eq14427
       grind)
    | exact superpose eq14427 eq266
    | exact resolve eq266 eq14427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq14427
  have eq15639 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15624
       have i₂ := eq14395
       grind)
    | exact superpose eq14395 eq15624
    | exact resolve eq15624 eq14395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14395 eq15624
  have eq15643 : ∀ X0 : G, x = (M.op x (M.op X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq15618 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15618
    | (have j0 := eq15618 X0
       grind)
    | exact resolve eq15618 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15618
  have eq15647 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15639
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15639
    | exact resolve eq15639 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15639
  have eq15650 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15647
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15647
    | exact resolve eq15647 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15647
  have eq15651 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq15650
  have eq15653 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15651 eq20
    | exact resolve eq20 eq15651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15715 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq15760 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15653
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15653
    | exact resolve eq15653 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq15653
  have eq15790 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15760 eq147
    | exact resolve eq147 eq15760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq15760
  have eq15910 : (k (M.op x y) y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq154 eq15790
    | exact resolve eq15790 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq15790
  have eq15926 : y = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq222 eq15910
    | exact resolve eq15910 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq15910
  have eq17902 : y ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15926 eq3603
    | (have j0 := eq3603 (M.op x y)
       grind)
    | exact resolve eq3603 eq15926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3603 eq15926
  have eq17929 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17902
       have r₂ := eq15651
       grind)
    | exact resolve eq17902 eq15651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17902
  have eq18775 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17929 eq15643
    | exact resolve eq15643 eq17929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15643 eq17929
  have eq18811 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq18775
  have eq18820 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq15651 eq18811
    | exact resolve eq18811 eq15651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15651 eq18811
  have eq18842 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18820
       have r₂ := eq15715
       grind)
    | exact resolve eq18820 eq15715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15715 eq18820
  have eq18843 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18842
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18842
    | exact resolve eq18842 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq18842
  have eq18844 : x = (M.op x y) := by grind
  clear eq18843
  have eq18847 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq18844 eq20
    | exact resolve eq20 eq18844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq18844
  have eq18956 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq18847
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18847
    | exact resolve eq18847 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq18847
  have eq18963 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq18956 eq26
    | exact resolve eq26 eq18956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq19035 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18956 eq14461
    | exact resolve eq14461 eq18956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14461 eq18956
  have eq19043 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq19035
       have r₂ := eq27
       grind)
    | exact resolve eq19035 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19035
  have eq19121 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18963 eq893
    | exact resolve eq893 eq18963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq19139 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq19121
       have r₂ := eq27
       grind)
    | exact resolve eq19121 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19121
  have eq19175 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (M.op (σ (M.op x y)) (σ y)))) := by
    intro X0
    first
    | exact superpose eq19043 eq14
    | exact resolve eq14 eq19043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19043
  have eq19204 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq18963 eq19175
    | exact resolve eq19175 eq18963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19175
  have eq19218 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq19139 eq19204
    | exact resolve eq19204 eq19139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19139 eq19204
  have eq19982 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq926 eq19218
    | exact resolve eq19218 eq926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926 eq19218
  have eq20015 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq19982
  have eq20022 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18963 eq20015
    | exact resolve eq20015 eq18963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18963 eq20015
  have eq20035 : False := by grind
  exact eq20035

/-- `Equation4364`: `x ◇ (y ◇ z) = y ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_pxx_pxy_Equation4364 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4364 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4364.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X1 (M.op X2 X0)) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq73 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq73 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq73
    | exact resolve eq73 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq565 : (M.op x y) = (k x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq568 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF2 sF3
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq571 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq582 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq565
       grind)
    | exact superpose eq565 eq41
    | exact resolve eq41 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq583 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq582
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq582
    | exact resolve eq582 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq585 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq583
    | exact resolve eq583 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq595 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq585 eq568
    | exact resolve eq568 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568 eq585
  have eq602 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq595
       have r₂ := eq27
       grind)
    | exact resolve eq595 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq610 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op (σ y) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq602 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) x
       have r₂ := eq602
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq602
       grind)
    | exact resolve eq13 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq610 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq625 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq611 eq602
    | exact resolve eq602 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602 eq611
  have eq633 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq625
  have eq643 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq633 eq153
    | exact resolve eq153 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq633
  have eq646 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq32 eq643
    | exact resolve eq643 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq643
  have eq649 : y = (M.op y y) := by
    first
    | (have j1 := eq571 y
       grind)
    | (have r₁ := eq646
       have r₂ := eq571 y
       grind)
    | exact resolve eq646 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq655 : ∀ X0 : G, (M.op X0 y) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq649
       grind)
    | exact superpose eq649 eq16
    | exact resolve eq16 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq656 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq649
       grind)
    | exact superpose eq649 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq649
       grind)
    | exact resolve eq13 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq657 : ∀ X0 : G, (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq656 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq658 : ∀ X0 : G, (M.op X0 y) = (k y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq655 X0
       have i₂ := eq657 (M.op y X0)
       grind)
    | exact superpose eq657 eq655
    | exact resolve eq655 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq661 : ∀ X0 : G, (k y (k y X0)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq658 X0
       have i₂ := eq657 X0
       grind)
    | exact superpose eq657 eq658
    | exact resolve eq658 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq679 : y = (k y y) := by
    first
    | (have i₁ := eq649
       have i₂ := eq657 y
       grind)
    | exact superpose eq657 eq649
    | exact resolve eq649 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649 eq657
  have eq690 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq679
       grind)
    | exact superpose eq679 eq41
    | exact resolve eq41 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq679
  have eq693 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq690
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq690
    | exact resolve eq690 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq690
  have eq768 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq693 eq571
    | (have j0 := eq571 (σ y)
       grind)
    | (have r₁ := eq571 (σ y)
       have r₂ := eq693
       grind)
    | exact resolve eq571 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571 eq693
  have eq769 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq768
  have eq779 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq769 eq16
    | exact resolve eq16 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq781 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | exact superpose eq769 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) x
       have r₂ := eq769
       grind)
    | exact resolve eq13 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq782 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq781 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq784 : ∀ X0 : G, (M.op X0 (σ y)) = (k (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq782 eq779
    | exact resolve eq779 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq788 : ∀ X0 : G, (M.op X0 (σ y)) = (k (σ y) (k (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq782 eq784
    | exact resolve eq784 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782 eq784
  have eq842 : ∀ X0 : G, (k (σ y) (σ (k y X0))) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq37 (k y X0)
       have i₂ := eq661 X0
       grind)
    | exact superpose eq661 eq37
    | exact resolve eq37 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq843 : ∀ X0 : G, (k (σ y) (k (σ y) (σ X0))) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq842 X0
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq842
    | exact resolve eq842 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq842
  have eq848 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq788 eq843
    | exact resolve eq843 eq788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788 eq843
  have eq970 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq848 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq848
    | (have j0 := eq848 x
       grind)
    | exact resolve eq848 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq848
  have eq997 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq970
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq970
    | exact resolve eq970 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq970
  have eq1002 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq997
    | exact resolve eq997 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq997
  have eq1005 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1002
    | exact resolve eq1002 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1002
  have eq1007 : False := by grind
  exact eq1007

/-- `Equation4412`: `x ◇ (x ◇ y) = (y ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_pyx_pxy_Equation4412 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4412 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4412.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
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
  have eq213 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq12 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7880 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq214 x y
       grind)
    | exact superpose eq214 eq16
    | (have j1 := eq214 y y
       grind)
    | exact resolve eq16 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7883 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq213 X1 (σ X0)
       have i₂ := eq214 X0 X0
       grind)
    | exact superpose eq214 eq213
    | (have j0 := eq213 X1 (σ X0)
       have j1 := eq214 X0 X0
       grind)
    | (have r₁ := eq213 X0 (σ X1)
       have r₂ := eq214 X0 X1
       grind)
    | (have r₁ := eq213 X0 (σ X0)
       have r₂ := eq214 X0 X1
       grind)
    | exact resolve eq213 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7884 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq214 X0 X0
       grind)
    | exact superpose eq214 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq214 X0 X0
       grind)
    | (have r₁ := eq12 (σ X1) X1
       have r₂ := eq214 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) X1
       have r₂ := eq214 X0 X1
       grind)
    | exact resolve eq12 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7886 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq214 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq7887 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq7886 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7886
  have eq7889 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq7884 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7884
  have eq7890 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq7883 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7883
  have eq7893 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq7889 X0 X1
       have j1 := eq12 (σ X0) X1
       grind)
    | (have r₁ := eq7889 X0 X1
       have r₂ := eq12 (σ X0) X1
       grind)
    | exact resolve eq7889 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7889
  have eq7894 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq7890 X0 X1
       have j1 := eq213 X1 (σ X0)
       grind)
    | (have r₁ := eq7890 X0 X1
       have r₂ := eq213 X0 (σ X0)
       grind)
    | exact resolve eq7890 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7890
  have eq7917 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7887 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq7887
    | (have j0 := eq7887 (τ X0)
       grind)
    | exact resolve eq7887 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq7887
  have eq7929 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7917 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7917
    | (have j0 := eq7917 X0
       grind)
    | exact resolve eq7917 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7917
  have eq7946 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
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
  have eq7981 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq7946 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq7946
    | (have j0 := eq7946 (τ X0)
       grind)
    | exact resolve eq7946 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7946
  have eq9288 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq7880
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq7880
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq7880 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7880
  have eq9291 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq9288
  have eq9527 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq213 X0 (σ y)
       have i₂ := eq9291
       grind)
    | exact superpose eq9291 eq213
    | (have j0 := eq213 X0 (σ y)
       grind)
    | (have r₁ := eq213 X0 (σ y)
       have r₂ := eq9291
       grind)
    | (have r₁ := eq213 X0 (σ x)
       have r₂ := eq9291
       grind)
    | (have r₁ := eq213 X0 y
       have r₂ := eq9291
       grind)
    | exact resolve eq213 eq9291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9528 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq9527 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9527
  have eq9899 : (τ (σ y)) ≠ (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq7981 (σ y)
       have i₂ := eq9528 (σ y)
       grind)
    | exact superpose eq9528 eq7981
    | (have j0 := eq7981 (σ y)
       grind)
    | exact resolve eq7981 eq9528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9528
  have eq10019 : y ≠ (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9899
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq9899
    | exact resolve eq9899 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9899
  have eq10030 : y = (M.op y y) ∨ y ≠ (τ (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10019
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq10019
    | exact resolve eq10019 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10019
  have eq10031 : y ≠ (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq10030
  have eq10034 : y ≠ (τ (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10031
       have i₂ := eq9291
       grind)
    | exact superpose eq9291 eq10031
    | exact resolve eq10031 eq9291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9291 eq10031
  have eq10043 : y ≠ (τ (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq10034
  have eq10044 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq10043
       have r₂ := eq10 y
       grind)
    | exact resolve eq10043 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10043
  have eq10047 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq213 X0 (σ x)
       have i₂ := eq10044
       grind)
    | exact superpose eq10044 eq213
    | (have j0 := eq213 X0 (σ x)
       grind)
    | (have r₁ := eq213 X0 (σ x)
       have r₂ := eq10044
       grind)
    | (have r₁ := eq213 X0 y
       have r₂ := eq10044
       grind)
    | (have r₁ := eq213 X0 x
       have r₂ := eq10044
       grind)
    | exact resolve eq213 eq10044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10048 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq10047 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10047
  have eq10085 : (τ (M.op (σ x) (σ x))) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq7981 (σ x)
       have i₂ := eq10048 (σ x)
       grind)
    | exact superpose eq10048 eq7981
    | (have j0 := eq7981 (σ x)
       grind)
    | exact resolve eq7981 eq10048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7981 eq10048
  have eq10205 : x ≠ (τ (M.op (σ x) (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10085
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10085
    | exact resolve eq10085 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10085
  have eq10216 : x = (M.op x x) ∨ x ≠ (τ (M.op (σ x) (σ x))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10205
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10205
    | exact resolve eq10205 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10205
  have eq10217 : x ≠ (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq10216
  have eq10220 : x ≠ (τ (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10217
       have i₂ := eq10044
       grind)
    | exact superpose eq10044 eq10217
    | exact resolve eq10217 eq10044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10044 eq10217
  have eq10229 : x ≠ (τ (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq10220
  have eq10230 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq10229
       have r₂ := eq10 x
       grind)
    | exact resolve eq10229 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10229
  have eq10231 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq10230
       grind)
    | exact superpose eq10230 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq10230
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq10230
       grind)
    | exact resolve eq12 eq10230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10232 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq213 X0 y
       have i₂ := eq10230
       grind)
    | exact superpose eq10230 eq213
    | (have j0 := eq213 X0 y
       grind)
    | (have r₁ := eq213 X0 y
       have r₂ := eq10230
       grind)
    | (have r₁ := eq213 X0 x
       have r₂ := eq10230
       grind)
    | exact resolve eq213 eq10230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10233 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq10232 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10232
  have eq10234 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq10231 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10231
  have eq10291 : ∀ X0 : G, (k X0 (τ y)) = (τ (M.op y (σ X0))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq28 X0 y
       have i₂ := eq10233 (σ X0)
       grind)
    | exact superpose eq10233 eq28
    | exact resolve eq28 eq10233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq10387 : ∀ X0 : G, (k (τ y) X0) = (τ (M.op (σ X0) y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq22 y X0
       have i₂ := eq10234 (σ X0)
       grind)
    | exact superpose eq10234 eq22
    | exact resolve eq22 eq10234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq10403 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op (τ X0) y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq18 X0 y
       have i₂ := eq10234 (τ X0)
       grind)
    | exact superpose eq10234 eq18
    | exact resolve eq18 eq10234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq10234
  have eq10431 : ∀ X0 : G, (τ (M.op y X0)) = (k (τ X0) (τ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10291 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10291
    | exact resolve eq10291 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10291
  have eq10507 : ∀ X0 : G, (τ (k X0 y)) = (τ (M.op y X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10431 X0
       have i₂ := eq31 y X0
       grind)
    | exact superpose eq31 eq10431
    | exact resolve eq10431 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10431
  have eq10542 : ∀ X0 X1 : G, (τ (k (k X0 y) X1)) = (k (τ (M.op y X0)) (τ X1)) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 (k X0 y)
       have i₂ := eq10507 X0
       grind)
    | exact superpose eq10507 eq31
    | exact resolve eq31 eq10507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10631 : ∀ X0 X1 : G, (τ (k (k X0 y) X1)) = (τ (k (M.op y X0) X1)) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq10542 X0 X1
       have i₂ := eq31 X1 (M.op y X0)
       grind)
    | exact superpose eq31 eq10542
    | exact resolve eq10542 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10542
  have eq10861 : ∀ X0 : G, (τ (M.op X0 y)) = (k (τ y) (τ X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10387 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10387
    | exact resolve eq10387 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10387
  have eq10942 : ∀ X0 : G, (τ (M.op X0 y)) = (τ (k y X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10861 X0
       have i₂ := eq31 X0 y
       grind)
    | exact superpose eq31 eq10861
    | exact resolve eq10861 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10861
  have eq10976 : ∀ X0 X1 : G, (τ (k X1 (k y X0))) = (k (τ X1) (τ (M.op X0 y))) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (k y X0) X1
       have i₂ := eq10942 X0
       grind)
    | exact superpose eq10942 eq31
    | exact resolve eq31 eq10942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10942
  have eq11069 : ∀ X0 X1 : G, (τ (k X1 (M.op X0 y))) = (τ (k X1 (k y X0))) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq10976 X0 X1
       have i₂ := eq31 (M.op X0 y) X1
       grind)
    | exact superpose eq31 eq10976
    | exact resolve eq10976 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10976
  have eq11080 : ∀ X0 : G, (σ (M.op X0 y)) = (k (σ y) (σ X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10403 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10403
    | exact resolve eq10403 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10403
  have eq11166 : ∀ X0 : G, (σ (M.op X0 y)) = (σ (k y X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq11080 X0
       have i₂ := eq15 y X0
       grind)
    | exact superpose eq15 eq11080
    | exact resolve eq11080 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11080
  have eq11350 : ∀ X0 : G, (τ (k (M.op y X0) y)) = (τ (M.op y (k X0 y))) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10507 (k X0 y)
       have i₂ := eq10631 X0 y
       grind)
    | exact superpose eq10631 eq10507
    | exact resolve eq10507 eq10631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10507 eq10631
  have eq11408 : ∀ X0 : G, (τ (k (M.op y X0) y)) = (τ (M.op y (k X0 y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq11350 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11350
  have eq12995 : ∀ X0 X1 : G, (k X0 (k y X1)) = (σ (τ (k X0 (M.op X1 y)))) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 (k y X1))
       have i₂ := eq11069 X1 X0
       grind)
    | exact superpose eq11069 eq11
    | exact resolve eq11 eq11069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11069
  have eq13107 : ∀ X0 X1 : G, (k X0 (M.op X1 y)) = (k X0 (k y X1)) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq12995 X0 X1
       have i₂ := eq11 (k X0 (M.op X1 y))
       grind)
    | exact superpose eq11 eq12995
    | exact resolve eq12995 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12995
  have eq13747 : (τ (k y y)) = (τ (M.op y (k y y))) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11408 y
       have i₂ := eq10230
       grind)
    | exact superpose eq10230 eq11408
    | exact resolve eq11408 eq10230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11408
  have eq13830 : (τ (k y y)) = (τ (M.op y (k y y))) ∨ x = (M.op x x) := by grind
  clear eq13747
  have eq13877 : (τ (M.op y y)) = (τ (M.op y (M.op y y))) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13830
       have i₂ := eq10233 y
       grind)
    | exact superpose eq10233 eq13830
    | exact resolve eq13830 eq10233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13830
  have eq13941 : (τ (M.op y y)) = (τ (M.op y (M.op y y))) ∨ x = (M.op x x) := by grind
  clear eq13877
  have eq13988 : (τ y) = (τ (M.op y y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13941
       have i₂ := eq10230
       grind)
    | exact superpose eq10230 eq13941
    | exact resolve eq13941 eq10230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13941
  have eq14048 : (τ y) = (τ (M.op y y)) ∨ x = (M.op x x) := by grind
  clear eq13988
  have eq14104 : ∀ X0 : G, (k (τ y) (τ X0)) = (τ (k (M.op y y) X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq31 X0 (M.op y y)
       have i₂ := eq14048
       grind)
    | exact superpose eq14048 eq31
    | exact resolve eq31 eq14048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14048
  have eq14203 : ∀ X0 : G, (τ (k y X0)) = (τ (k (M.op y y) X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq14104 X0
       have i₂ := eq31 X0 y
       grind)
    | exact superpose eq31 eq14104
    | exact resolve eq14104 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq14104
  have eq14363 : ∀ X0 : G, (σ (τ (k y X0))) = (k (M.op y y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq11 (k (M.op y y) X0)
       have i₂ := eq14203 X0
       grind)
    | exact superpose eq14203 eq11
    | exact resolve eq11 eq14203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14203
  have eq14479 : ∀ X0 : G, (k y X0) = (k (M.op y y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq14363 X0
       have i₂ := eq11 (k y X0)
       grind)
    | exact superpose eq11 eq14363
    | exact resolve eq14363 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14363
  have eq14597 : ∀ X0 : G, (k y (k y X0)) = (k (M.op y y) (M.op X0 y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq13107 (M.op y y) X0
       have i₂ := eq14479 (k y X0)
       grind)
    | exact superpose eq14479 eq13107
    | exact resolve eq13107 eq14479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13107 eq14479
  have eq14622 : ∀ X0 : G, (k y (k y X0)) = (k (M.op y y) (M.op X0 y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq14597 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14597
  have eq32544 : (k y y) = (k y (k y y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14622 y
       have i₂ := eq10230
       grind)
    | exact superpose eq10230 eq14622
    | exact resolve eq14622 eq10230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14622
  have eq32610 : (k y y) = (k y (k y y)) ∨ x = (M.op x x) := by grind
  clear eq32544
  have eq32650 : (M.op y y) = (k y (M.op y y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq32610
       have i₂ := eq10233 y
       grind)
    | exact superpose eq10233 eq32610
    | exact resolve eq32610 eq10233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10233 eq32610
  have eq32765 : (M.op y y) = (k y (M.op y y)) ∨ x = (M.op x x) := by grind
  clear eq32650
  have eq32767 : y = (k y y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq32765
       have i₂ := eq10230
       grind)
    | exact superpose eq10230 eq32765
    | exact resolve eq32765 eq10230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10230 eq32765
  have eq32884 : y = (k y y) ∨ x = (M.op x x) := by grind
  clear eq32767
  have eq32977 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq7893 y X0
       have i₂ := eq32884
       grind)
    | exact superpose eq32884 eq7893
    | (have j0 := eq7893 y X0
       grind)
    | exact resolve eq7893 eq32884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7893 eq32884
  have eq33070 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq32977 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32977
  have eq33968 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq33070 (σ X0)
       have i₂ := eq15 y X0
       grind)
    | exact superpose eq15 eq33070
    | exact resolve eq33070 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33070
  have eq35823 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq33968 x
       grind)
    | exact superpose eq33968 eq16
    | exact resolve eq16 eq33968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33968
  have eq35894 : x = (M.op x x) := by
    first
    | (have r₁ := eq35823
       have r₂ := eq11166 x
       grind)
    | exact resolve eq35823 eq11166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11166 eq35823
  have eq35897 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq213 X0 x
       have i₂ := eq35894
       grind)
    | exact superpose eq35894 eq213
    | (have j0 := eq213 X0 x
       grind)
    | (have r₁ := eq213 X0 x
       have r₂ := eq35894
       grind)
    | exact resolve eq213 eq35894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq35898 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq35897 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35897
  have eq35918 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq7894 x X0
       have i₂ := eq35898 x
       grind)
    | exact superpose eq35898 eq7894
    | (have j0 := eq7894 x X0
       grind)
    | exact resolve eq7894 eq35898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7894
  have eq36062 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq35918 X0
       have i₂ := eq35894
       grind)
    | exact superpose eq35894 eq35918
    | (have j0 := eq35918 X0
       grind)
    | exact resolve eq35918 eq35894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35894 eq35918
  have eq36063 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq36062 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36062
  have eq36922 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq36063 (σ X0)
       grind)
    | exact superpose eq36063 eq15
    | exact resolve eq15 eq36063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36063
  have eq37014 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq36922 X0
       have i₂ := eq35898 X0
       grind)
    | exact superpose eq35898 eq36922
    | exact resolve eq36922 eq35898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35898 eq36922
  have eq38400 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq37014 y
       grind)
    | exact superpose eq37014 eq16
    | (have r₁ := eq16
       have r₂ := eq37014 y
       grind)
    | exact resolve eq16 eq37014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37014
  have eq38423 : False := by grind
  exact eq38423

/-- `Equation4426`: `x ◇ (x ◇ y) = (z ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_y_pxx_y_pxy_Equation4426 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4426 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4426.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X3) := by
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
  clear eq35
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
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
  have eq176 : ∀ X0 X1 X4 X5 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X4 X4) X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq16 x x X4 X5
       have i₂ := eq16 x x X0 X1
       grind)
    | (have i₁ := eq16 (M.op x x) X1 x x
       have i₂ := eq16 X0 X1 x (M.op (M.op x x) X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 x x
       have i₂ := eq16 X2 X3 x x
       grind)
    | (have i₁ := eq16 X0 X1 X2 (M.op (M.op X2 X2) X1)
       have i₂ := eq16 (M.op X2 X2) X1 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq179 X2 X3 X4 (M.op X4 x)
       have i₂ := eq179 X4 x X0 X1
       grind)
    | (have i₁ := eq179 X2 X3 X4 (M.op X4 x)
       have i₂ := eq179 X0 X1 X4 x
       grind)
    | exact superpose eq179 eq179
    | exact resolve eq179 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq580 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq179 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq179
    | (have j0 := eq179 X0 X1 x y
       grind)
    | exact resolve eq179 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq581 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq179
    | (have j0 := eq179 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq179 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq600 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq580 x x
       have i₂ := eq581 x x
       grind)
    | (have i₁ := eq580 (σ x) (σ y)
       have i₂ := eq581 x x
       grind)
    | exact superpose eq581 eq580
    | (have j0 := eq580 (σ x) (σ y)
       have j1 := eq581 x y
       grind)
    | exact resolve eq580 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq602 : ∀ X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq575 x x X2 X3 X4
       have i₂ := eq581 x x
       grind)
    | (have i₁ := eq575 (σ x) (σ y) X2 X3 X4
       have i₂ := eq581 x x
       grind)
    | exact superpose eq581 eq575
    | (have j0 := eq575 (σ x) (σ y) X2 X3 X4
       grind)
    | exact resolve eq575 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq608 : ∀ X4 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X4 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X4
    first
    | (have i₁ := eq602 x x X4
       have i₂ := eq581 x x
       grind)
    | (have i₁ := eq602 (σ x) (σ y) X4
       have i₂ := eq581 x x
       grind)
    | exact superpose eq581 eq602
    | (have j0 := eq602 (σ x) (σ y) X4
       grind)
    | exact resolve eq602 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq640 : ∀ X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X2 X3
    first
    | (have i₁ := eq176 x (M.op (M.op x x) x) X2 X3
       have i₂ := eq581 (M.op x x) x
       grind)
    | exact superpose eq581 eq176
    | exact resolve eq176 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq657 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op X0 X0) = (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq608 eq13
    | (have j0 := eq13 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq13 x (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq608 x
       grind)
    | exact resolve eq13 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq608 eq16
    | exact resolve eq16 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have j0 := eq657 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq666 : ∀ X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) X2) := by
    intro X2
    first
    | (have i₁ := eq661 x x X2
       have i₂ := eq581 x x
       grind)
    | (have i₁ := eq661 (σ x) (σ y) X2
       have i₂ := eq581 x x
       grind)
    | exact superpose eq581 eq661
    | (have j0 := eq661 (σ x) (σ y) X2
       grind)
    | exact resolve eq661 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq709 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (k X0 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq581 X0 X0
       have i₂ := eq665 X0
       grind)
    | exact superpose eq665 eq581
    | exact resolve eq581 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq712 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) ≠ X0 ∨ (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq665 X0
       grind)
    | exact superpose eq665 eq13
    | exact resolve eq13 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq715 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq640 X0 X1
       have i₂ := eq665 X0
       grind)
    | exact superpose eq665 eq640
    | exact resolve eq640 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq719 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op X0 X0) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq640 X0 (M.op X0 X0)
       have i₂ := eq665 (M.op X0 X0)
       grind)
    | exact superpose eq665 eq640
    | exact resolve eq640 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq750 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) ≠ X0 ∨ (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) = (k (M.op (σ x) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq666 eq13
    | (have j0 := eq13 (M.op (σ x) (M.op (σ x) (σ y))) X0
       grind)
    | (have r₁ := eq13 (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq666 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq13 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq764 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) X0) ∨ (M.op (σ x) (M.op (σ x) (σ y))) ≠ X0 := by
    intro X0
    first
    | exact superpose eq608 eq750
    | (have j0 := eq750 X0
       grind)
    | (have r₁ := eq750 (M.op x (M.op (σ x) (M.op (σ x) (σ y))))
       have r₂ := eq608 x
       grind)
    | exact resolve eq750 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq933 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) ∨ (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 ∨ (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq665 X0
       grind)
    | exact superpose eq665 eq11
    | exact resolve eq11 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq944 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) X0) ∨ (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) = X0 ∨ (M.op (σ x) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq666 eq11
    | (have j0 := eq11 (M.op (σ x) (M.op (σ x) (σ y))) X0
       grind)
    | exact resolve eq11 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq946 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
  have eq948 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq999 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) ∨ (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have j0 := eq933 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933
  have eq1024 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) X0) ∨ (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have j0 := eq944 X0
       have j1 := eq764 X0
       grind)
    | (have r₁ := eq944 X0
       have r₂ := eq764 (k (M.op (σ x) (M.op (σ x) (σ y))) X0)
       grind)
    | (have r₁ := eq944 (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq764 (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y))))
       grind)
    | (have r₁ := eq944 X0
       have r₂ := eq764 X0
       grind)
    | exact resolve eq944 eq764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq1032 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq999 X0
       have j1 := eq712 X0
       grind)
    | (have r₁ := eq999 X0
       have r₂ := eq712 X0
       grind)
    | exact resolve eq999 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712 eq999
  have eq1044 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = X0 ∨ (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq608 eq1024
    | (have j0 := eq1024 X0
       grind)
    | exact resolve eq1024 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq1063 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | (have j0 := eq1044 (k (M.op (σ x) (M.op (σ x) (σ y))) X0)
       have j1 := eq764 X0
       grind)
    | (have r₁ := eq1044 X0
       have r₂ := eq764 X0
       grind)
    | (have r₁ := eq1044 (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq764 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq1044 X0
       have r₂ := eq764 (k (M.op (σ x) (M.op (σ x) (σ y))) X0)
       grind)
    | exact resolve eq1044 eq764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764 eq1044
  have eq1100 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (k X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq715 (M.op sF2 sF4) X1
       have i₂ := eq1032 (M.op sF2 sF4)
       grind)
    | exact superpose eq1032 eq715
    | exact resolve eq715 eq1032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq1101 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq709 (M.op sF2 sF4)
       have i₂ := eq1032 (M.op sF2 sF4)
       grind)
    | exact superpose eq1032 eq709
    | exact resolve eq709 eq1032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq1102 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq665 (M.op sF2 sF4)
       have i₂ := eq1032 (M.op sF2 sF4)
       grind)
    | exact superpose eq1032 eq665
    | exact resolve eq665 eq1032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq1174 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (k X0 X0) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq719 X0
       have i₂ := eq1102 X0
       grind)
    | exact superpose eq1102 eq719
    | exact resolve eq719 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq1215 : (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (k (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ y)) := by
    first
    | exact superpose eq1063 eq40
    | exact resolve eq40 eq1063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063
  have eq1242 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (k X0 X0) X1) ∨ (M.op (k X0 X0) (k X0 X0)) = X1 ∨ (M.op (σ x) (M.op (σ x) (σ y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X0) X1
       have i₂ := eq1100 X0 X1
       grind)
    | exact superpose eq1100 eq11
    | (have j0 := eq11 (k X0 X0) X1
       grind)
    | exact resolve eq11 eq1100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1246 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) ≠ X1 ∨ (M.op (k X0 X0) (k X0 X0)) = (k (k X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (k X0 X0) X1
       have i₂ := eq1100 X0 X1
       grind)
    | exact superpose eq1100 eq13
    | (have j0 := eq13 (k X0 X0) X1
       grind)
    | (have r₁ := eq13 (k X0 X0) (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq1100 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq13 eq1100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100
  have eq1252 : ∀ X0 X1 : G, (k (k X0 X0) (M.op (σ x) (M.op (σ x) (σ y)))) = (k (k X0 X0) X1) ∨ (M.op (σ x) (M.op (σ x) (σ y))) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1246 X0 X1
       have i₂ := eq665 (k X0 X0)
       grind)
    | exact superpose eq665 eq1246
    | (have j0 := eq1246 X0 X1
       grind)
    | exact resolve eq1246 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246
  have eq1255 : ∀ X0 X1 : G, (k (k X0 X0) (M.op (σ x) (M.op (σ x) (σ y)))) = X1 ∨ (M.op (σ x) (M.op (σ x) (σ y))) = (k (k X0 X0) X1) ∨ (M.op (σ x) (M.op (σ x) (σ y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1242 X0 X1
       have i₂ := eq665 (k X0 X0)
       grind)
    | exact superpose eq665 eq1242
    | (have j0 := eq1242 X0 X1
       grind)
    | exact resolve eq1242 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665 eq1242
  have eq1262 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (k X0 X0) X1) ∨ (M.op (σ x) (M.op (σ x) (σ y))) ≠ X1 := by
    intro X0 X1
    first
    | exact superpose eq1174 eq1252
    | (have j0 := eq1252 X0 X1
       grind)
    | (have r₁ := eq1252 X0 (k (k X0 X0) (M.op (σ x) (M.op (σ x) (σ y))))
       have r₂ := eq1174 X0
       grind)
    | exact resolve eq1252 eq1174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252
  have eq1263 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = X1 ∨ (M.op (σ x) (M.op (σ x) (σ y))) = (k (k X0 X0) X1) ∨ (M.op (σ x) (M.op (σ x) (σ y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1174 eq1255
    | (have j0 := eq1255 X0 X1
       grind)
    | exact resolve eq1255 eq1174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174 eq1255
  have eq1264 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = X1 ∨ (M.op (σ x) (M.op (σ x) (σ y))) = (k (k X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1263 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263
  have eq1266 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (k X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1264 X0 (k (k X0 X0) X1)
       have j1 := eq1262 X0 X1
       grind)
    | (have r₁ := eq1264 X0 X1
       have r₂ := eq1262 X0 X1
       grind)
    | (have r₁ := eq1264 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq1262 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq1264 X0 X1
       have r₂ := eq1262 X0 (k (k X0 X0) X1)
       grind)
    | exact resolve eq1264 eq1262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262 eq1264
  have eq1271 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1101 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1101
    | exact resolve eq1101 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1324 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ (k X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1266 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1266
    | exact resolve eq1266 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1662 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ (M.op (σ x) (M.op (σ x) (σ y)))) X1) := by
    intro X1
    first
    | (have i₁ := eq1324 (k x x) X1
       have i₂ := eq1266 x (k x x)
       grind)
    | exact superpose eq1266 eq1324
    | exact resolve eq1324 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1679 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (σ (k (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X0) X1
       have i₂ := eq1324 X0 (σ X1)
       grind)
    | exact superpose eq1324 eq10
    | exact resolve eq10 eq1324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1682 : ∀ X0 : G, (τ (M.op (σ x) (M.op (σ x) (σ y)))) = (k (k X0 X0) y) := by
    intro X0
    first
    | (have i₁ := eq72 (k X0 X0)
       have i₂ := eq1324 X0 sF3
       grind)
    | exact superpose eq1324 eq72
    | exact resolve eq72 eq1324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq1324
  have eq1711 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1682 x
       have i₂ := eq1266 x y
       grind)
    | exact superpose eq1266 eq1682
    | exact resolve eq1682 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1682
  have eq1714 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1679 x x
       have i₂ := eq1266 x x
       grind)
    | exact superpose eq1266 eq1679
    | exact resolve eq1679 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266 eq1679
  have eq4559 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq946
       grind)
    | exact superpose eq946 eq40
    | exact resolve eq40 eq946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq946
  have eq4560 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4559
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4559
    | exact resolve eq4559 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4559
  have eq4562 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq4560
    | exact resolve eq4560 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4560
  have eq4564 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4562
       have i₂ := eq1102 x
       grind)
    | exact superpose eq1102 eq4562
    | exact resolve eq4562 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4562
  have eq12147 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4564 eq948
    | exact resolve eq948 eq4564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948 eq4564
  have eq12158 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12147
       have r₂ := eq27
       grind)
    | exact resolve eq12147 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12147
  have eq12164 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12158
       have i₂ := eq1102 sF2
       grind)
    | exact superpose eq1102 eq12158
    | exact resolve eq12158 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102 eq12158
  have eq12166 : (τ (σ y)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12164 eq97
    | exact resolve eq97 eq12164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq12164
  have eq12230 : y = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq12166
    | exact resolve eq12166 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12166
  have eq12231 : y = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq12230
  have eq12245 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1101 x
       have i₂ := eq12231
       grind)
    | exact superpose eq12231 eq1101
    | exact resolve eq1101 eq12231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101
  have eq12252 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1271 x
       have i₂ := eq12231
       grind)
    | exact superpose eq12231 eq1271
    | exact resolve eq1271 eq12231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271 eq12231
  have eq12298 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12252
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12252
    | exact resolve eq12252 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12252
  have eq12300 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12245
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12245
    | exact resolve eq12245 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12245
  have eq12312 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12298
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12298
    | exact resolve eq12298 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq12298
  have eq12315 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq12312
    | exact resolve eq12312 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12312
  have eq12316 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12300 eq12315
    | exact resolve eq12315 eq12300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12315
  have eq12319 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12316 eq608
    | exact resolve eq608 eq12316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq12376 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12316 eq1711
    | exact resolve eq1711 eq12316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12378 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq12381 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq12376
    | exact resolve eq12376 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12376
  have eq12438 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq12319
    | (have j0 := eq12319 X0
       grind)
    | exact resolve eq12319 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12319
  have eq12441 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12316 eq12381
    | exact resolve eq12381 eq12316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12381
  have eq12497 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12316 eq12438
    | exact resolve eq12438 eq12316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12316 eq12438
  have eq12498 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq12441
    | exact resolve eq12441 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12441
  have eq12585 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12498 eq27
    | exact resolve eq27 eq12498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12498
  have eq12894 : (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12300 eq1714
    | exact resolve eq1714 eq12300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1714 eq12300
  have eq12911 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq12894
    | exact resolve eq12894 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12894
  have eq13078 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12911 eq1711
    | exact resolve eq1711 eq12911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1711
  have eq13086 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq13078
    | exact resolve eq13078 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13078
  have eq13147 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12911 eq13086
    | exact resolve eq13086 eq12911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13086
  have eq13205 : y = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq13147
    | exact resolve eq13147 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq13147
  have eq13248 : y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq13205
       have r₂ := eq12585
       grind)
    | exact resolve eq13205 eq12585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12585 eq13205
  have eq13268 : (M.op x y) = (M.op x (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq13248
       grind)
    | exact superpose eq13248 eq18
    | exact resolve eq18 eq13248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13280 : (M.op x y) ≠ (σ y) ∨ y = (M.op x y) := by grind
  clear eq13248
  have eq15320 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12497 eq13268
    | exact resolve eq13268 eq12497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12497 eq13268
  have eq15325 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq15320
  have eq15331 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq15325
       have r₂ := eq12378
       grind)
    | exact resolve eq15325 eq12378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12378 eq15325
  have eq15424 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15331 eq27
    | exact resolve eq27 eq15331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15486 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15331 eq12911
    | exact resolve eq12911 eq15331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12911 eq15331
  have eq15487 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq15486
  have eq15491 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq15487
       have r₂ := eq13280
       grind)
    | exact resolve eq15487 eq13280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13280 eq15487
  have eq15533 : y = (M.op x y) := by
    first
    | (have r₁ := eq15491
       have r₂ := eq15424
       grind)
    | exact resolve eq15491 eq15424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15424 eq15491
  have eq15553 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq15533
       grind)
    | exact superpose eq15533 eq18
    | exact resolve eq18 eq15533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq15554 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq15533
       grind)
    | exact superpose eq15533 eq24
    | exact resolve eq24 eq15533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq15533
  have eq15580 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq15554 eq20
    | exact resolve eq20 eq15554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15554
  have eq15704 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq15553 eq600
    | exact resolve eq600 eq15553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600 eq15553
  have eq15758 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq15704 eq1215
    | exact resolve eq1215 eq15704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215
  have eq15789 : ∀ X0 : G, (M.op x y) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq15704 eq1662
    | exact resolve eq1662 eq15704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1662
  have eq15799 : (M.op x y) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq15704 eq581
    | exact resolve eq581 eq15704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581 eq15704
  have eq15810 : ∀ X0 : G, (M.op x y) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq20 eq15789
    | (have j0 := eq15789 X0
       grind)
    | exact resolve eq15789 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15789
  have eq15837 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq15758
    | exact resolve eq15758 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq15758
  have eq15858 : ∀ X0 : G, (M.op x y) = (k (σ y) X0) := by
    intro X0
    first
    | exact superpose eq15580 eq15810
    | exact resolve eq15810 eq15580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15810
  have eq15878 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq15580 eq15837
    | exact resolve eq15837 eq15580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15837
  have eq15895 : (M.op x y) = (σ y) := by
    first
    | exact superpose eq15858 eq15878
    | exact resolve eq15878 eq15858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15858 eq15878
  have eq15914 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq15895 eq26
    | exact resolve eq26 eq15895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq15961 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15799 eq15914
    | exact resolve eq15914 eq15799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15799 eq15914
  have eq15993 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq15961 eq27
    | exact resolve eq27 eq15961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq15961
  have eq16116 : (M.op x y) ≠ (σ y) := by
    first
    | exact superpose eq15580 eq15993
    | exact resolve eq15993 eq15580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15580 eq15993
  have eq16158 : False := by grind
  exact eq16158
