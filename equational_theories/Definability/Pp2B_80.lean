import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4533`: `x ◇ (y ◇ z) = (y ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_x_pxx_pxy_Equation4533 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4533 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4533.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X2) X2) := by
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
  clear eq36
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
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq177 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X0 (M.op X1 X2)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq16 X3 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X0 X1 X2
       have i₂ := eq16 (M.op (M.op X0 X1) X1) X0 X1
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq188 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) y)) = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq179 eq188
    | exact resolve eq188 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq562 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
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
  have eq568 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
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
  have eq575 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq576 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq575 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq1187 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq576 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq576
    | (have j0 := eq576 (σ X0)
       grind)
    | exact resolve eq576 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1832 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (M.op X0 X1) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x (M.op X0 X1) X1
       have i₂ := eq185 X0 X1 x
       grind)
    | exact superpose eq185 eq16
    | exact resolve eq16 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2320 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X1) ∨ (k X1 (M.op (M.op X0 X1) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op (M.op X0 X1) X1)
       have i₂ := eq1832 X0 X1
       grind)
    | exact superpose eq1832 eq13
    | (have j0 := eq13 X1 (M.op (M.op X0 X1) X1)
       grind)
    | (have r₁ := eq13 X1 (M.op (M.op X0 X1) X1)
       have r₂ := eq1832 X0 X1
       grind)
    | exact resolve eq13 eq1832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1832
  have eq2382 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X1) X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2320 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2320
  have eq2461 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2382 x (M.op X0 X1)
       have i₂ := eq16 (M.op x (M.op X0 X1)) X0 X1
       grind)
    | exact superpose eq16 eq2382
    | exact resolve eq2382 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2472 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq193 eq2382
    | exact resolve eq2382 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq2496 : ∀ X0 : G, (τ (σ y)) = (k y (τ (M.op (M.op X0 (σ y)) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq107 (M.op (M.op X0 sF3) sF3)
       have i₂ := eq2382 X0 sF3
       grind)
    | exact superpose eq2382 eq107
    | exact resolve eq107 eq2382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq2382
  have eq2497 : ∀ X0 : G, y = (k y (τ (M.op (M.op X0 (σ y)) (σ y)))) := by
    intro X0
    first
    | exact superpose eq31 eq2496
    | exact resolve eq2496 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2496
  have eq3877 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq562
       grind)
    | exact superpose eq562 eq40
    | exact resolve eq40 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq562
  have eq3878 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq3877
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3877
    | exact resolve eq3877 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3877
  have eq3880 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq3878
    | exact resolve eq3878 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3878
  have eq26530 : (σ (M.op (M.op x y) y)) ≠ (σ (M.op (M.op x y) y)) ∨ (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq2472 eq1187
    | (have j0 := eq1187 (M.op (M.op x y) y)
       grind)
    | exact resolve eq1187 eq2472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187 eq2472
  have eq26568 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by grind
  clear eq26530
  have eq27357 : ∀ X0 X1 : G, (M.op X0 (σ (M.op (M.op x y) y))) = (M.op X1 (σ (M.op (M.op x y) y))) := by
    intro X0 X1
    first
    | exact superpose eq26568 eq181
    | exact resolve eq181 eq26568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27519 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (M.op X0 (σ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq27357 eq26568
    | exact resolve eq26568 eq27357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26568 eq27357
  have eq27560 : ∀ X0 X1 : G, (σ (M.op X0 (M.op x y))) = (M.op X1 (σ (M.op X0 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq179 eq27519
    | exact resolve eq27519 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27519
  have eq29809 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq3880 eq568
    | exact resolve eq568 eq3880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568 eq3880
  have eq29818 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq29809
       have r₂ := eq27
       grind)
    | exact resolve eq29809 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29809
  have eq29826 : y = (k y (τ (M.op (σ y) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29818 eq2497
    | exact resolve eq2497 eq29818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2497
  have eq29863 : y = (k y (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29818 eq29826
    | exact resolve eq29826 eq29818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29818 eq29826
  have eq29865 : y = (k y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq31 eq29863
    | exact resolve eq29863 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29863
  have eq29866 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y y) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq29865
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq29865
       have r₂ := eq13 y y
       grind)
    | (have r₁ := eq29865
       have r₂ := eq13 x y
       grind)
    | exact resolve eq29865 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29865
  have eq29893 : (σ y) = (k (σ y) (M.op (σ y) (σ x))) ∨ y = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29866 eq2461
    | exact resolve eq2461 eq29866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2461
  have eq29902 : (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29866 eq29893
    | exact resolve eq29893 eq29866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29866 eq29893
  have eq36111 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29902 eq152
    | exact resolve eq152 eq29902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq29902
  have eq36120 : y = (k y y) ∨ y = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq31 eq36111
    | exact resolve eq36111 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq36111
  have eq36121 : y = (k y y) ∨ y = (M.op y x) := by grind
  clear eq36120
  have eq36134 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq576 y
       have i₂ := eq36121
       grind)
    | exact superpose eq36121 eq576
    | (have j0 := eq576 y
       grind)
    | (have r₁ := eq576 y
       have r₂ := eq36121
       grind)
    | exact resolve eq576 eq36121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576 eq36121
  have eq36137 : y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq36134
  have eq36169 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq181 X0 y y x
       have i₂ := eq36137
       grind)
    | exact superpose eq36137 eq181
    | exact resolve eq181 eq36137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq36532 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq36169 x X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq36169 X0 x
       grind)
    | exact superpose eq36169 eq18
    | (have j1 := eq36169 x X0
       grind)
    | exact resolve eq18 eq36169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36169
  have eq36709 : y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq36137
       have i₂ := eq36532 y
       grind)
    | exact superpose eq36532 eq36137
    | exact resolve eq36137 eq36532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36137 eq36532
  have eq36735 : y = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq36709
  have eq36797 : ∀ X0 : G, (M.op y x) = (M.op X0 (M.op y x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq185 y x x
       have i₂ := eq36735
       grind)
    | exact superpose eq36735 eq185
    | exact resolve eq185 eq36735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq36833 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq36735 eq36797
    | exact resolve eq36797 eq36735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36735 eq36797
  have eq36967 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq36833 x
       grind)
    | exact superpose eq36833 eq18
    | (have j1 := eq36833 x
       grind)
    | exact resolve eq18 eq36833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36833
  have eq36990 : y = (M.op x y) := by grind
  clear eq36967
  have eq37008 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq36990
       grind)
    | exact superpose eq36990 eq18
    | exact resolve eq18 eq36990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq37009 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq36990
       grind)
    | exact superpose eq36990 eq24
    | exact resolve eq24 eq36990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq37100 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq179 eq37008
    | exact resolve eq37008 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq37008
  have eq37102 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq37100
       have i₂ := eq36990
       grind)
    | exact superpose eq36990 eq37100
    | exact resolve eq37100 eq36990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36990 eq37100
  have eq37104 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq37009 eq20
    | exact resolve eq20 eq37009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37009
  have eq37579 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq37102 eq27560
    | exact resolve eq27560 eq37102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27560 eq37102
  have eq37619 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq37579
    | (have j0 := eq37579 X0
       grind)
    | exact resolve eq37579 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq37579
  have eq37632 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq37104 eq37619
    | exact resolve eq37619 eq37104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37619
  have eq37914 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37632 eq26
    | (have j1 := eq37632 (σ x)
       grind)
    | exact resolve eq26 eq37632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq37632
  have eq38005 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq37914 eq27
    | exact resolve eq27 eq37914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq37914
  have eq38086 : False := by grind
  exact eq38086

/-- `Equation455`: `x = x ◇ (y ◇ (z ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pxy_pxy_pyx_Equation455 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law455 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law455.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
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
  have eq175 : ∀ X0 : G, (M.op X0 (M.op y (M.op x (M.op x y)))) = X0 := by
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
  have eq176 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y))))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) X0
       have i₂ := eq16 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X1 X1) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X1 X1) X0
       have i₂ := eq179 X1 X0
       grind)
    | exact superpose eq179 eq13
    | (have j0 := eq13 (M.op X1 X1) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X1
       have r₂ := eq179 X0 X1
       grind)
    | exact resolve eq13 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 : G, (k (M.op X1 X1) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq188 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq396 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq698 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (M.op X0 X0)
       have i₂ := eq179 X0 (M.op X0 X0)
       grind)
    | exact superpose eq179 eq28
    | (have j0 := eq28 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq28 X0 (M.op X0 X0)
       have r₂ := eq179 X0 (M.op X0 X0)
       grind)
    | exact resolve eq28 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq712 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq698 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq721 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq712 X0 X1
       have i₂ := eq179 X0 X1
       grind)
    | exact superpose eq179 eq712
    | exact resolve eq712 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq735 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq396 X0 (M.op X1 X1)
       have i₂ := eq721 X1 (σ X0)
       grind)
    | exact superpose eq721 eq396
    | exact resolve eq396 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq736 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 (M.op X1 X1)
       have i₂ := eq721 X1 (τ X0)
       grind)
    | exact superpose eq721 eq35
    | exact resolve eq35 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq721
  have eq749 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq736 X0 X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq736
    | exact resolve eq736 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq750 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq735 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq735
    | exact resolve eq735 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq845 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq846 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq847 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq28
    | (have j0 := eq28 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq897 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq847 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq910 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq897 X0 X1
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq897 X1 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq897 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq897
  have eq1476 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ (M.op X0 X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq910 (σ (M.op X0 X0)) X1
       have i₂ := eq749 (σ (M.op X0 X0)) X0
       grind)
    | exact superpose eq749 eq910
    | (have j0 := eq910 (σ (M.op X0 X0)) X1
       grind)
    | (have r₁ := eq910 (σ (M.op X1 X1)) X1
       have r₂ := eq749 (σ (M.op X1 X1)) X1
       grind)
    | exact resolve eq910 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1479 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ (M.op X0 X0))) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq910 (τ (M.op X0 X0)) X1
       have i₂ := eq750 (τ (M.op X0 X0)) X0
       grind)
    | exact superpose eq750 eq910
    | (have j0 := eq910 (τ (M.op X0 X0)) X1
       grind)
    | (have r₁ := eq910 (τ (M.op X1 X1)) X1
       have r₂ := eq750 (τ (M.op X1 X1)) X1
       grind)
    | exact resolve eq910 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq1486 : ∀ X0 X1 : G, (k X1 (τ (M.op X0 X0))) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq1479 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479
  have eq1489 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq1476 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1476
  have eq1498 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1486 X0 X1
       have i₂ := eq750 X1 X0
       grind)
    | exact superpose eq750 eq1486
    | exact resolve eq1486 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750 eq1486
  have eq1501 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1489 X0 X1
       have i₂ := eq749 X1 X0
       grind)
    | exact superpose eq749 eq1489
    | exact resolve eq1489 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749 eq1489
  have eq1515 : ∀ X0 : G, (M.op X0 (τ (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))))) = X0 := by
    intro X0
    first
    | exact superpose eq176 eq1498
    | exact resolve eq1498 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1577 : ∀ X0 : G, (M.op X0 (σ (M.op y (M.op x (M.op x y))))) = X0 := by
    intro X0
    first
    | exact superpose eq175 eq1501
    | exact resolve eq1501 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq3000 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq845
       grind)
    | exact superpose eq845 eq40
    | exact resolve eq40 eq845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq845
  have eq3002 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3000
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3000
    | exact resolve eq3000 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3000
  have eq3004 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq3002
    | exact resolve eq3002 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3002
  have eq9497 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3004 eq846
    | exact resolve eq846 eq3004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846 eq3004
  have eq9509 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9497
       have r₂ := eq27
       grind)
    | exact resolve eq9497 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9497
  have eq9656 : ∀ X0 : G, (M.op X0 (τ (σ x))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9509 eq1498
    | exact resolve eq1498 eq9509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498 eq9509
  have eq9714 : ∀ X0 : G, x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30 eq9656
    | exact resolve eq9656 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq9656
  have eq10269 : x ≠ x ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq9714 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9714
  have eq10270 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10269
  have eq10352 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq190 X0 x
       have i₂ := eq10270
       grind)
    | exact superpose eq10270 eq190
    | exact resolve eq190 eq10270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq10384 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1501 x X0
       have i₂ := eq10270
       grind)
    | exact superpose eq10270 eq1501
    | exact resolve eq1501 eq10270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1501 eq10270
  have eq10444 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10384 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10384
    | (have j0 := eq10384 X0
       grind)
    | exact resolve eq10384 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10384
  have eq10750 : ∀ X0 : G, X0 ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10444 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) X0
       have r₂ := eq10444 X0
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq10444 X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq10444 X0
       grind)
    | exact resolve eq13 eq10444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10444
  have eq10784 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq10750 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10750
  have eq11362 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq10352 y
       grind)
    | exact superpose eq10352 eq18
    | (have j1 := eq10352 y
       grind)
    | exact resolve eq18 eq10352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10352
  have eq11732 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq11362
       grind)
    | exact superpose eq11362 eq41
    | exact resolve eq41 eq11362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq11362
  have eq11736 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11732
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11732
    | exact resolve eq11732 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11732
  have eq11738 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq11736
    | exact resolve eq11736 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11736
  have eq12241 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10784 eq26
    | (have j1 := eq10784 (σ y)
       grind)
    | exact resolve eq26 eq10784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10784
  have eq12546 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11738 eq12241
    | exact resolve eq12241 eq11738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11738 eq12241
  have eq12580 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12546
       have r₂ := eq27
       grind)
    | exact resolve eq12546 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12546
  have eq12617 : ∀ X0 : G, (M.op X0 (τ (M.op (σ y) (M.op (σ x) (σ x))))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12580 eq1515
    | exact resolve eq1515 eq12580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1515 eq12580
  have eq12649 : ∀ X0 : G, (M.op X0 (τ (σ y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12617 X0
       have i₂ := eq179 sF2 sF3
       grind)
    | exact superpose eq179 eq12617
    | exact resolve eq12617 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12617
  have eq12684 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq32 eq12649
    | exact resolve eq12649 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq12649
  have eq13357 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq12684 x
       grind)
    | exact superpose eq12684 eq18
    | (have j1 := eq12684 x
       grind)
    | exact resolve eq18 eq12684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq12684
  have eq13362 : x = (M.op x y) := by grind
  clear eq13357
  have eq13370 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq13362
       grind)
    | exact superpose eq13362 eq22
    | exact resolve eq22 eq13362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq13412 : ∀ X0 : G, (M.op X0 (σ (M.op y (M.op (M.op x y) (M.op x y))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1577 X0
       have i₂ := eq13362
       grind)
    | exact superpose eq13362 eq1577
    | exact resolve eq1577 eq13362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1577 eq13362
  have eq13440 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13412 X0
       have i₂ := eq179 sF0 y
       grind)
    | exact superpose eq179 eq13412
    | exact resolve eq13412 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq13412
  have eq13484 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13440 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13440
    | (have j0 := eq13440 X0
       grind)
    | exact resolve eq13440 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq13440
  have eq13508 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13370 eq20
    | exact resolve eq20 eq13370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq13370
  have eq13995 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13484 eq26
    | (have j1 := eq13484 (σ x)
       grind)
    | exact resolve eq26 eq13484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq13484
  have eq14075 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq13995 eq27
    | exact resolve eq27 eq13995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq13995
  have eq14172 : False := by grind
  exact eq14172

/-- `Equation455`: `x = x ◇ (y ◇ (z ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_x_pxy_Equation455 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law455 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law455.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq21 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq9 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq21 X0 (M.op X0 X0)
       grind)
    | exact superpose eq21 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq21 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq36 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq34
    | exact resolve eq34 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq40 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op X1 X1)
       have i₂ := eq36 X1 (τ X0)
       grind)
    | exact superpose eq36 eq17
    | exact resolve eq17 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq40
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq46 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (M.op X1 X1))
       have i₂ := eq41 (τ X0) X1
       grind)
    | exact superpose eq41 eq17
    | exact resolve eq17 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq46
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq54 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (M.op X1 X1)))
       have i₂ := eq47 (τ X0) X1
       grind)
    | exact superpose eq47 eq17
    | exact resolve eq17 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (M.op X1 X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq54
    | exact resolve eq54 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq61 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq74 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31
    | exact resolve eq31 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 (M.op X1 X1)
       have i₂ := eq36 X1 (σ X0)
       grind)
    | exact superpose eq36 eq61
    | exact resolve eq61 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq89
    | exact resolve eq89 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq132 : ∀ X0 X1 X2 : G, (k X2 (τ (M.op X0 (M.op X1 (M.op X1 X0))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq102 X2 (M.op X0 (M.op X1 (M.op X1 X0)))
       have i₂ := eq9 (M.op X0 (M.op X1 (M.op X1 X0))) X0 X1
       grind)
    | exact superpose eq9 eq102
    | exact resolve eq102 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 (τ (M.op X1 X1))
       have i₂ := eq102 (σ X0) X1
       grind)
    | exact superpose eq102 eq61
    | exact resolve eq61 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq141 : ∀ X0 X1 : G, (k X0 (τ (τ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq136 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq136
    | exact resolve eq136 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq147 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 (τ (τ (M.op X1 X1)))
       have i₂ := eq141 (σ X0) X1
       grind)
    | exact superpose eq141 eq61
    | exact resolve eq61 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq152 : ∀ X0 X1 : G, (k X0 (τ (τ (τ (M.op X1 X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq147 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq147
    | exact resolve eq147 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq193 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (M.op X1 X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (M.op X1 X1))))
       have i₂ := eq55 (τ X0) X1
       grind)
    | exact superpose eq55 eq17
    | exact resolve eq17 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (M.op X1 X1)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq193 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq193
    | exact resolve eq193 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq203 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X0 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq68
    | exact resolve eq68 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X0 (k X1 (τ X0))
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq68
    | exact resolve eq68 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ X1) (M.op (σ X0) (σ (k X0 X1))))) = X2 ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X1) (σ X0)
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq9
    | (have j1 := eq68 X0 X1
       grind)
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq68 X0 X0
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq68 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq68 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq68 X0 X1
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq68 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq220 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq219 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq228 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq210 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq232 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq228 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq228 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq228 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq243 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (τ (M.op X1 X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 (τ (τ (τ (M.op X1 X1))))
       have i₂ := eq152 (σ X0) X1
       grind)
    | exact superpose eq152 eq61
    | exact resolve eq61 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq250 : ∀ X0 X1 : G, (k X0 (τ (τ (τ (τ (M.op X1 X1)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq243 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq243
    | exact resolve eq243 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq304 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (M.op X1 X1))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (σ (M.op X1 X1)))))
       have i₂ := eq196 (τ X0) X1
       grind)
    | exact superpose eq196 eq17
    | exact resolve eq17 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq310 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (M.op X1 X1))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq304 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq304
    | exact resolve eq304 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq319 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (τ (τ (M.op X1 X1))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 (τ (τ (τ (τ (M.op X1 X1)))))
       have i₂ := eq250 (σ X0) X1
       grind)
    | exact superpose eq250 eq61
    | exact resolve eq61 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq326 : ∀ X0 X1 : G, (k X0 (τ (τ (τ (τ (τ (M.op X1 X1))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq319 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq319
    | exact resolve eq319 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq671 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (τ (τ (τ (M.op X1 X1)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 (τ (τ (τ (τ (τ (M.op X1 X1))))))
       have i₂ := eq326 (σ X0) X1
       grind)
    | exact superpose eq326 eq61
    | exact resolve eq61 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq676 : ∀ X0 X1 : G, (k X0 (τ (τ (τ (τ (τ (τ (M.op X1 X1)))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq671 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq671
    | exact resolve eq671 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq961 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ (M.op X0 X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq232 (M.op X0 X0) X1
       have i₂ := eq36 X0 (M.op X0 X0)
       grind)
    | exact superpose eq36 eq232
    | (have j0 := eq232 (M.op X0 X0) X1
       grind)
    | exact resolve eq232 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq964 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (k X1 (σ (σ (M.op X0 X0)))) = (M.op X1 (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq232 (σ (M.op X0 X0)) X1
       have i₂ := eq41 (σ (M.op X0 X0)) X0
       grind)
    | exact superpose eq41 eq232
    | (have j0 := eq232 (σ (M.op X0 X0)) X1
       grind)
    | exact resolve eq232 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq967 : ∀ X0 X1 : G, (σ (σ (σ (M.op X0 X0)))) ≠ (σ (σ (σ (M.op X0 X0)))) ∨ (k X1 (σ (σ (σ (M.op X0 X0))))) = (M.op X1 (σ (σ (σ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq232 (σ (σ (M.op X0 X0))) X1
       have i₂ := eq47 (σ (σ (M.op X0 X0))) X0
       grind)
    | exact superpose eq47 eq232
    | (have j0 := eq232 (σ (σ (M.op X0 X0))) X1
       grind)
    | exact resolve eq232 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq983 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq232 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq232
    | (have j0 := eq232 (τ X0) X1
       grind)
    | exact resolve eq232 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq996 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (M.op X0 X0))))) = (M.op X1 (σ (σ (σ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have j0 := eq967 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967
  have eq999 : ∀ X0 X1 : G, (k X1 (σ (σ (M.op X0 X0)))) = (M.op X1 (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq964 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964
  have eq1002 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq961 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961
  have eq1004 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq983 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq983
    | (have j0 := eq983 X0 X1
       grind)
    | exact resolve eq983 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983
  have eq1018 : ∀ X0 X1 : G, (M.op X1 (σ (σ (σ (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq996 X0 X1
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq996
    | exact resolve eq996 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq996
  have eq1021 : ∀ X0 X1 : G, (M.op X1 (σ (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq999 X0 X1
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq999
    | exact resolve eq999 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq999
  have eq1024 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1002 X0 X1
       have i₂ := eq41 X1 X0
       grind)
    | exact superpose eq41 eq1002
    | exact resolve eq1002 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1002
  have eq1025 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1004 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1004
    | (have j0 := eq1004 X0 X1
       grind)
    | exact resolve eq1004 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq1232 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (σ (σ (M.op X0 X0))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq310 X1 (σ (σ (M.op X0 X0)))
       have i₂ := eq1021 X0 (σ (σ (M.op X0 X0)))
       grind)
    | exact superpose eq1021 eq310
    | exact resolve eq310 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq1400 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (σ (σ (σ (M.op X0 X0)))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq310 X1 (σ (σ (σ (M.op X0 X0))))
       have i₂ := eq1018 X0 (σ (σ (σ (M.op X0 X0))))
       grind)
    | exact superpose eq1018 eq310
    | exact resolve eq310 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310 eq1018
  have eq3042 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (τ X1)) (M.op (σ (τ X0)) (σ (τ (k X0 X1)))))) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq209 (τ X0) (τ X1) X2
       have i₂ := eq74 X1 X0
       grind)
    | exact superpose eq74 eq209
    | (have j0 := eq209 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq209 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq209
  have eq3133 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (τ X1)) (M.op (σ (τ X0)) (k X0 X1)))) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3042 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq3042
    | (have j0 := eq3042 X0 X1 X2
       grind)
    | exact resolve eq3042 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3042
  have eq3145 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (τ X1)) (M.op X0 (k X0 X1)))) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3133 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3133
    | (have j0 := eq3133 X0 X1 X2
       grind)
    | exact resolve eq3133 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3133
  have eq3154 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 (M.op X0 (k X0 X1)))) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3145 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3145
    | (have j0 := eq3145 X0 X1 X2
       grind)
    | exact resolve eq3145 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3145
  have eq3155 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X2 (M.op X1 (M.op X0 (k X0 X1)))) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3154 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3154
    | (have j0 := eq3154 X0 X1 X2
       grind)
    | exact resolve eq3154 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3154
  have eq3156 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X1 ∨ (M.op X2 (M.op X1 (M.op X0 (k X0 X1)))) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3155 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3155
    | (have j0 := eq3155 X0 X1 X2
       grind)
    | exact resolve eq3155 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3155
  have eq3157 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 (M.op X0 (k X0 X1)))) = X2 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3156 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3156
    | (have j0 := eq3156 X0 X1 X2
       grind)
    | exact resolve eq3156 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3156
  have eq3866 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (σ X2) = (k (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (σ X2) (k X0 (σ X1))
       have i₂ := eq203 X0 X1 X2
       grind)
    | exact superpose eq203 eq13
    | (have j0 := eq13 (σ X2) (k X0 (σ X1))
       have j1 := eq203 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X2) (k X0 (σ X1))
       have r₂ := eq203 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k X0 (σ X1)) (k X0 (σ X1))
       have r₂ := eq203 X0 X1 X2
       grind)
    | exact resolve eq13 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq3880 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (σ X2) = (k (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3866 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3866
  have eq3881 : ∀ X0 X1 X2 : G, (σ X2) = (k (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3880 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3880
  have eq3882 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (σ X2) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3881 X0 X1 X2
       have i₂ := eq29 X0 X1 X2
       grind)
    | exact superpose eq29 eq3881
    | (have j0 := eq3881 X0 X1 X2
       grind)
    | exact resolve eq3881 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3881
  have eq4193 : ∀ X0 X1 X2 : G, (k X0 (σ (k X1 (τ X2)))) = (M.op (σ (τ X0)) (k (σ X1) X2)) ∨ (k (σ X1) X2) = (M.op (σ (τ X0)) (k (σ X1) X2)) ∨ (k (σ X1) X2) = (M.op (k (σ X1) X2) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (k X1 (τ X2))
       have i₂ := eq204 X1 X2 (τ X0)
       grind)
    | exact superpose eq204 eq17
    | (have j1 := eq204 X1 X2 (τ X0)
       grind)
    | exact resolve eq17 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq204
  have eq4241 : ∀ X0 X1 X2 : G, (k X0 (σ (k X1 (τ X2)))) = (M.op X0 (k (σ X1) X2)) ∨ (k (σ X1) X2) = (M.op (σ (τ X0)) (k (σ X1) X2)) ∨ (k (σ X1) X2) = (M.op (k (σ X1) X2) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4193 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4193
    | (have j0 := eq4193 X0 X1 X2
       grind)
    | exact resolve eq4193 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4193
  have eq4258 : ∀ X0 X1 X2 : G, (k X0 (k (σ X1) X2)) = (M.op X0 (k (σ X1) X2)) ∨ (k (σ X1) X2) = (M.op (σ (τ X0)) (k (σ X1) X2)) ∨ (k (σ X1) X2) = (M.op (k (σ X1) X2) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4241 X0 X1 X2
       have i₂ := eq18 X2 X1
       grind)
    | exact superpose eq18 eq4241
    | (have j0 := eq4241 X0 X1 X2
       grind)
    | exact resolve eq4241 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4241
  have eq4273 : ∀ X0 X1 X2 : G, (k X0 (k (σ X1) X2)) = (M.op X0 (k (σ X1) X2)) ∨ (k (σ X1) X2) = (M.op (σ (τ X0)) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4258 X0 X1 X2
       have j1 := eq12 X0 (k (σ X1) X2)
       grind)
    | (have r₁ := eq4258 X0 X1 X2
       have r₂ := eq12 X0 (k (σ X1) X2)
       grind)
    | exact resolve eq4258 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4258
  have eq4288 : ∀ X0 X1 X2 : G, (k (σ X1) X2) = (M.op X0 (k (σ X1) X2)) ∨ (k X0 (k (σ X1) X2)) = (M.op X0 (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4273 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4273
    | (have j0 := eq4273 X0 X1 X2
       grind)
    | exact resolve eq4273 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4273
  have eq22614 : ∀ X0 X2 : G, (k X2 (σ X0)) = (M.op X2 (σ X0)) ∨ (σ X0) = (M.op X2 (σ X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq4288 X0 x (τ (τ (τ (τ (τ (τ (M.op x x)))))))
       have i₂ := eq676 (σ x) x
       grind)
    | exact superpose eq676 eq4288
    | exact resolve eq4288 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676 eq4288
  have eq70536 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (σ X2) = (σ (k X2 (k (τ X0) (σ (σ (σ (σ (σ (σ (σ (M.op X1 X1))))))))))) ∨ (M.op (σ X2) X0) = (σ (k X2 (k (τ X0) (σ (σ (σ (σ (σ (σ (σ (M.op X1 X1))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3882 X1 (σ (σ (σ (σ (σ (σ (σ (M.op X0 X0)))))))) X2
       have i₂ := eq1400 X0 X1
       grind)
    | exact superpose eq1400 eq3882
    | (have j0 := eq3882 X0 (σ (σ (σ (σ (σ (σ (σ (M.op X1 X1)))))))) X2
       grind)
    | exact resolve eq3882 eq1400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400 eq3882
  have eq70674 : ∀ X0 X1 X2 : G, (σ X2) = (σ (k X2 (τ X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op (σ X2) X0) = (σ (k X2 (k (τ X0) (σ (σ (σ (σ (σ (σ (σ (M.op X1 X1))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70536 X0 X1 X2
       have i₂ := eq1232 X1 (τ X0)
       grind)
    | exact superpose eq1232 eq70536
    | (have j0 := eq70536 X0 X1 X2
       grind)
    | exact resolve eq70536 eq1232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70536
  have eq70716 : ∀ X0 X1 X2 : G, (σ X2) = (k (σ X2) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (σ X2) X0) = (σ (k X2 (k (τ X0) (σ (σ (σ (σ (σ (σ (σ (M.op X1 X1))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70674 X0 X1 X2
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq70674
    | (have j0 := eq70674 X0 X1 X2
       grind)
    | exact resolve eq70674 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70674
  have eq70747 : ∀ X0 X2 : G, (σ (k X2 (τ X0))) = (M.op (σ X2) X0) ∨ (σ X2) = (k (σ X2) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq70716 X0 x X2
       have i₂ := eq1232 x (τ X0)
       grind)
    | exact superpose eq1232 eq70716
    | (have j0 := eq70716 X0 x X2
       grind)
    | exact resolve eq70716 eq1232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1232 eq70716
  have eq70778 : ∀ X0 X2 : G, (M.op (σ X2) X0) = (k (σ X2) X0) ∨ (σ X2) = (k (σ X2) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq70747 X0 X2
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq70747
    | (have j0 := eq70747 X0 X2
       grind)
    | exact resolve eq70747 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq70747
  have eq70795 : ∀ X0 X2 : G, (σ X2) = (k (σ X2) X0) ∨ (M.op (σ X2) X0) = (k (σ X2) X0) := by
    intro X0 X2
    first
    | (have j0 := eq70778 X0 X2
       have j1 := eq12 (σ X2) X0
       grind)
    | (have r₁ := eq70778 x X2
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq70778 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70778
  have eq150205 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq22614 X1 X0
       grind)
    | exact superpose eq22614 eq31
    | (have j1 := eq22614 X1 X0
       grind)
    | exact resolve eq31 eq22614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22614
  have eq155585 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq70795 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq70795
    | exact resolve eq70795 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155631 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1
       have i₂ := eq70795 X1 X0
       grind)
    | exact superpose eq70795 eq61
    | (have j1 := eq70795 X1 X0
       grind)
    | exact resolve eq61 eq70795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq155816 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X0) X1
       have i₂ := eq70795 (σ X1) X0
       grind)
    | exact superpose eq70795 eq31
    | (have j1 := eq70795 (σ X1) X0
       grind)
    | exact resolve eq31 eq70795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq70795
  have eq155942 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq155816 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq155816
    | (have j0 := eq155816 X0 X1
       grind)
    | exact resolve eq155816 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155816
  have eq156057 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq155631 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq155631
    | (have j0 := eq155631 X0 X1
       grind)
    | exact resolve eq155631 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155631
  have eq156097 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq155942 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq155942
    | (have j0 := eq155942 X0 X1
       grind)
    | exact resolve eq155942 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155942
  have eq157066 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq155585 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158037 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (τ X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k (σ (τ X0)) X0) = (M.op (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq220 (τ X0)
       have i₂ := eq156057 (τ X0) X0
       grind)
    | exact superpose eq156057 eq220
    | (have j0 := eq220 (τ X0)
       have j1 := eq156057 (τ X0) X0
       grind)
    | exact resolve eq220 eq156057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq156057
  have eq158255 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k (σ (τ X0)) X0) = (M.op (σ (τ X0)) X0) := by
    intro X0
    first
    | (have j0 := eq158037 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158037
  have eq158435 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ (τ X0)) X0) = (M.op (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq158255 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq158255
    | (have j0 := eq158255 X0
       grind)
    | exact resolve eq158255 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158255
  have eq158526 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (σ (τ X0)) X0) := by
    intro X0
    first
    | (have j0 := eq158435 X0
       have j1 := eq12 (σ (τ X0)) X0
       grind)
    | (have r₁ := eq158435 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq158435 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158435
  have eq158548 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq158526 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq158526
    | exact resolve eq158526 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158526
  have eq164308 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq156097 x y
       grind)
    | exact superpose eq156097 eq16
    | (have j1 := eq156097 x y
       grind)
    | exact resolve eq16 eq156097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156097
  have eq164765 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq164308
       have i₂ := eq155585 x y
       grind)
    | exact superpose eq155585 eq164308
    | (have j1 := eq155585 x y
       grind)
    | exact resolve eq164308 eq155585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155585 eq164308
  have eq164774 : x = (M.op x y) ∨ x = (k x y) := by grind
  clear eq164765
  have eq164776 : x = (k x y) := by
    first
    | (have j1 := eq157066 x y
       grind)
    | (have r₁ := eq164774
       have r₂ := eq157066 x y
       grind)
    | exact resolve eq164774 eq157066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157066 eq164774
  have eq242057 : ∀ X0 : G, (M.op X0 (M.op y (M.op x x))) = X0 ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq3157 x y X0
       have i₂ := eq164776
       grind)
    | exact superpose eq164776 eq3157
    | (have j0 := eq3157 x y x
       grind)
    | exact resolve eq3157 eq164776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3157
  have eq242395 : ∀ X0 : G, y = (M.op y y) ∨ y = (M.op x y) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq242057 X0
       have i₂ := eq21 x y
       grind)
    | exact superpose eq21 eq242057
    | exact resolve eq242057 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242057
  have eq242549 : y ≠ y ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have j0 := eq242395 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242395
  have eq242550 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq242549
  have eq242594 : ∀ X0 : G, y = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq36 y X0
       have i₂ := eq242550
       grind)
    | exact superpose eq242550 eq36
    | exact resolve eq36 eq242550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq242550
  have eq1295580 : (σ (M.op x y)) ≠ (σ y) ∨ (k (τ (σ x)) y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq150205 (σ x) y
       grind)
    | exact superpose eq150205 eq16
    | (have j1 := eq150205 (σ x) y
       grind)
    | exact resolve eq16 eq150205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150205
  have eq1295595 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq1295580
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1295580
    | exact resolve eq1295580 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295580
  have eq1295947 : (σ (M.op x y)) ≠ (σ y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1295595
       have i₂ := eq164776
       grind)
    | exact superpose eq164776 eq1295595
    | exact resolve eq1295595 eq164776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164776 eq1295595
  have eq1296498 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq1295947
       have i₂ := eq242594 X0
       grind)
    | exact superpose eq242594 eq1295947
    | (have j1 := eq242594 X0
       grind)
    | exact resolve eq1295947 eq242594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242594 eq1295947
  have eq1296591 : ∀ X0 : G, x = (τ (M.op (σ x) (σ y))) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq1296498 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1296498
  have eq1301193 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq1296591 X0
       grind)
    | exact superpose eq1296591 eq11
    | (have j1 := eq1296591 X0
       grind)
    | exact resolve eq11 eq1296591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1296591
  have eq1307698 : ∀ X0 X1 : G, (k X0 (τ (M.op (σ y) (M.op (σ x) (σ x))))) = X0 ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq132 (σ y) (σ x) X0
       have i₂ := eq1301193 X1
       grind)
    | exact superpose eq1301193 eq132
    | (have j1 := eq1301193 X1
       grind)
    | exact resolve eq132 eq1301193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq1301193
  have eq1307810 : ∀ X0 X1 : G, (k X0 (τ (σ y))) = X0 ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1307698 X0 X1
       have i₂ := eq21 (σ x) (σ y)
       grind)
    | exact superpose eq21 eq1307698
    | (have j0 := eq1307698 X0 X1
       grind)
    | exact resolve eq1307698 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1307698
  have eq1307857 : ∀ X0 X1 : G, (k X0 y) = X0 ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1307810 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1307810
    | (have j0 := eq1307810 X0 X0
       grind)
    | exact resolve eq1307810 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1307810
  have eq1314095 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq1307857 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1307857
  have eq1314096 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq1314095 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314095
  have eq1314148 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq1025 y X0
       have i₂ := eq1314096 y
       grind)
    | exact superpose eq1314096 eq1025
    | (have j0 := eq1025 y X0
       grind)
    | (have r₁ := eq1025 y x
       have r₂ := eq1314096 y
       grind)
    | exact resolve eq1025 eq1314096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025
  have eq1314405 : y = (M.op y y) := by
    first
    | (have i₁ := eq158548 y
       have i₂ := eq1314096 y
       grind)
    | exact superpose eq1314096 eq158548
    | exact resolve eq158548 eq1314096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158548
  have eq1314685 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1314148 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314148
  have eq1314941 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq1314685 X0
       have i₂ := eq1314096 X0
       grind)
    | exact superpose eq1314096 eq1314685
    | exact resolve eq1314685 eq1314096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314096 eq1314685
  have eq1318862 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1024 y X0
       have i₂ := eq1314405
       grind)
    | exact superpose eq1314405 eq1024
    | exact resolve eq1024 eq1314405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024 eq1314405
  have eq1337971 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1318862 (σ x)
       grind)
    | exact superpose eq1318862 eq16
    | exact resolve eq16 eq1318862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318862
  have eq1338028 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1337971
       have i₂ := eq1314941 x
       grind)
    | exact superpose eq1314941 eq1337971
    | exact resolve eq1337971 eq1314941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314941 eq1337971
  have eq1338029 : False := by grind
  exact eq1338029

/-- `Equation4554`: `x ◇ (y ◇ z) = (z ◇ w) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_pyy_pyx_Equation4554 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4554 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4554.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X3) X2) := by
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq85 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
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
  have eq163 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq85 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq85
    | exact resolve eq85 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (M.op (M.op y X1) y) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X4) X0) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq16 x x X0 X4
       have i₂ := eq16 x x X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op (M.op x y) x) := by
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
  have eq184 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op X4 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X0 X1 X2 x
       have i₂ := eq16 X3 X4 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (k X0 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op X1 (k X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X0 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X1 X3 : G, (M.op X3 (M.op x y)) = (M.op (M.op (M.op X0 X1) X0) y) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq177 X3 (M.op x X0)
       have i₂ := eq16 y x X0 X1
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X2 : G, (M.op X0 (M.op x y)) = (M.op X2 (M.op x y)) := by
    intro X0 X2
    first
    | (have i₁ := eq177 X2 x
       have i₂ := eq177 X0 x
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 X2 : G, (M.op X0 (M.op x y)) = (M.op X1 (M.op X2 y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 y x
       have i₂ := eq177 X0 x
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq193 eq174
    | exact resolve eq174 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op (M.op X0 (M.op x y)) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq193 eq16
    | exact resolve eq16 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq232 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op y X0) y) := by
    intro X0
    first
    | exact superpose eq221 eq177
    | exact resolve eq177 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq241 : ∀ X0 X1 X3 : G, (M.op X3 (M.op (σ x) (σ y))) = (M.op (M.op (M.op X0 X1) X0) (σ y)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq178 X0 (M.op X1 x)
       have i₂ := eq16 sF3 X1 x X3
       grind)
    | exact superpose eq16 eq178
    | exact resolve eq178 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 X2 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X2 (M.op (σ x) (σ y))) := by
    intro X0 X2
    first
    | exact superpose eq178 eq178
    | exact resolve eq178 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X1 (M.op X2 (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq277 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq245 eq174
    | exact resolve eq174 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq303 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 (k x x)) := by
    intro X0
    first
    | (have i₁ := eq183 X0 x
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq183
    | exact resolve eq183 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq309 : ∀ X0 : G, (M.op (M.op x y) x) = (k (M.op X0 x) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq174 (M.op X0 x)
       have i₂ := eq183 (M.op X0 x) X0
       grind)
    | exact superpose eq183 eq174
    | exact resolve eq174 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq310 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op x y) x) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2 (M.op x x)
       have i₂ := eq183 X2 x
       grind)
    | exact superpose eq183 eq16
    | exact resolve eq16 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op X0 (k (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq184 X0 sF2
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq184
    | exact resolve eq184 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325 : ∀ X2 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) X2) (σ x)) := by
    intro X2
    first
    | exact superpose eq184 eq16
    | exact resolve eq16 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq326 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op X0 (σ x)) (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq184 eq174
    | exact resolve eq174 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X1 (k y y)) := by
    intro X0 X1
    first
    | (have i₁ := eq197 X0 X1 y
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq197
    | exact resolve eq197 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq398 : ∀ X1 : G, (k (M.op x y) (M.op x y)) = (M.op X1 (k y y)) := by
    intro X1
    first
    | exact superpose eq221 eq365
    | exact resolve eq365 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq438 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X1 (k (σ y) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq249 X0 X1 sF3
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq249
    | exact resolve eq249 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq471 : ∀ X1 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op X1 (k (σ y) (σ y))) := by
    intro X1
    first
    | exact superpose eq277 eq438
    | exact resolve eq438 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq485 : (M.op (M.op x y) x) = (k (k x x) (k x x)) := by
    first
    | (have i₁ := eq174 (k x x)
       have i₂ := eq303 (k x x)
       grind)
    | exact superpose eq303 eq174
    | exact resolve eq174 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq532 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | exact superpose eq320 eq174
    | exact resolve eq174 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq544 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (k (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq325 sF2
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq325
    | exact resolve eq325 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq817 : (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = y := by
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
  have eq822 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
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
  have eq1293 : (k (M.op x y) (M.op x y)) = (k (k y y) (k y y)) := by
    first
    | (have i₁ := eq174 (k y y)
       have i₂ := eq398 (k y y)
       grind)
    | exact superpose eq398 eq174
    | exact resolve eq174 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq1972 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq179 X0 X1 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq179
    | exact resolve eq179 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1983 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq179 X0 X1 (k x x)
       have i₂ := eq303 X0
       grind)
    | exact superpose eq303 eq179
    | exact resolve eq179 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq2003 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) := by
    intro X0 X1
    first
    | exact superpose eq277 eq179
    | exact resolve eq179 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq2229 : ∀ X0 : G, (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | (have i₁ := eq1983 X0 x
       have i₂ := eq2003 X0 x
       grind)
    | exact superpose eq2003 eq1983
    | exact resolve eq1983 eq2003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1983
  have eq2516 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op X3 (k X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq185 X1 X2 X0 X3 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq185
    | exact resolve eq185 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2519 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X3 (M.op X4 (M.op X5 X2))) = (M.op X6 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq185 X3 X4 (M.op X5 X2) X6 x
       have i₂ := eq185 x X5 X2 X0 X1
       grind)
    | (have i₁ := eq185 X3 X4 (M.op X5 X2) X6 x
       have i₂ := eq185 X0 X1 X2 x X5
       grind)
    | exact superpose eq185 eq185
    | exact resolve eq185 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2638 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (k (M.op X3 X2) (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq174 (M.op X3 X2)
       have i₂ := eq185 (M.op X3 X2) X3 X2 X0 X1
       grind)
    | (have i₁ := eq174 (M.op X3 X2)
       have i₂ := eq185 X0 X1 X2 (M.op X3 X2) X3
       grind)
    | exact superpose eq185 eq174
    | exact resolve eq174 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2649 : ∀ X0 X1 X2 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op X0 (M.op X1 X2)) y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq232 (M.op x X2)
       have i₂ := eq185 y x X2 X0 X1
       grind)
    | (have i₁ := eq232 (M.op x X2)
       have i₂ := eq185 X0 X1 X2 y x
       grind)
    | exact superpose eq185 eq232
    | exact resolve eq232 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq2955 : ∀ X0 X1 X2 X3 : G, (M.op (k X0 X0) X0) = (M.op X1 (M.op X2 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 X2 (M.op X3 X0) x
       have i₂ := eq188 X0 (M.op (M.op X3 X0) x) X3
       grind)
    | exact superpose eq188 eq16
    | exact resolve eq16 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3161 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = (M.op (k (M.op x y) (M.op x y)) X0) := by
    intro X0 X1
    first
    | exact superpose eq221 eq189
    | exact resolve eq189 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3211 : ∀ X0 X1 X3 : G, (M.op X0 (k X1 X1)) = (M.op X3 (k X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq189 X1 X3 x
       have i₂ := eq189 X1 X0 x
       grind)
    | exact superpose eq189 eq189
    | exact resolve eq189 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3347 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k (k X0 X0) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq174 (k X0 X0)
       have i₂ := eq189 X0 (k X0 X0) X1
       grind)
    | exact superpose eq189 eq174
    | exact resolve eq174 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3369 : ∀ X0 : G, (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) = (k (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3347 X0 x
       have i₂ := eq2003 X0 x
       grind)
    | exact superpose eq2003 eq3347
    | exact resolve eq3347 eq2003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2003 eq3347
  have eq3559 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op (M.op (k (M.op x y) (M.op x y)) X1) y) := by
    intro X0 X1
    first
    | exact superpose eq221 eq191
    | exact resolve eq191 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3610 : ∀ X0 X1 X2 : G, (M.op X2 (M.op x y)) = (M.op (M.op X0 (k X1 X1)) y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq191 X1 x X2
       have i₂ := eq189 X1 X0 x
       grind)
    | exact superpose eq189 eq191
    | exact resolve eq191 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq3757 : ∀ X0 X1 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op X0 (k X1 X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq221 eq3610
    | exact resolve eq3610 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3610
  have eq3808 : ∀ X1 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op (k (M.op x y) (M.op x y)) X1) y) := by
    intro X1
    first
    | exact superpose eq221 eq3559
    | exact resolve eq3559 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3559
  have eq4290 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ x) (σ y))) = (M.op (M.op X0 (k X1 X1)) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq241 X1 x X2
       have i₂ := eq189 X1 X0 x
       grind)
    | exact superpose eq189 eq241
    | exact resolve eq241 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq241
  have eq4445 : ∀ X0 X1 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (k X1 X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq277 eq4290
    | exact resolve eq4290 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277 eq4290
  have eq5105 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op x y) x) X0) = (M.op X1 (M.op X2 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq188 (M.op X3 X0) X1 X2
       have i₂ := eq310 (k (M.op X3 X0) (M.op X3 X0)) X3 X0
       grind)
    | exact superpose eq310 eq188
    | exact resolve eq188 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq5239 : ∀ X0 X1 X2 X3 : G, (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) = (M.op X1 (M.op X2 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq2229 eq5105
    | exact resolve eq5105 eq2229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2229 eq5105
  have eq5953 : ∀ X0 : G, (M.op (k X0 X0) X0) = (M.op (k (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq221 eq1972
    | exact resolve eq1972 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1972
  have eq6426 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 (k X1 X1)) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq325 (M.op x X0)
       have i₂ := eq2516 X0 sF2 x x
       grind)
    | exact superpose eq2516 eq325
    | exact resolve eq325 eq2516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325 eq2516
  have eq6860 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op X2 (M.op X3 (M.op X4 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq188 (M.op X4 X1) X2 X3
       have i₂ := eq222 X0 (k (M.op X4 X1) (M.op X4 X1)) X4 X1
       grind)
    | exact superpose eq222 eq188
    | exact resolve eq188 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq222
  have eq7024 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6860 X0 X1 x x x
       have i₂ := eq5239 X1 x x x
       grind)
    | exact superpose eq5239 eq6860
    | exact resolve eq6860 eq5239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5239 eq6860
  have eq7168 : ∀ X1 : G, (M.op (k (M.op x y) (M.op x y)) X1) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1) := by
    intro X1
    first
    | exact superpose eq221 eq7024
    | exact resolve eq7024 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7024
  have eq12224 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq817
       grind)
    | exact superpose eq817 eq39
    | exact resolve eq39 eq817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq12225 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq12224
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12224
    | exact resolve eq12224 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12224
  have eq12227 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq20 eq12225
    | exact resolve eq12225 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12225
  have eq12870 : ∀ X0 X1 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op X1 (σ (k X0 X0))) y) := by
    intro X0 X1
    first
    | (have i₁ := eq3757 X1 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq3757
    | exact resolve eq3757 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3757
  have eq12991 : ∀ X0 X1 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X1 (σ (k X0 X0))) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq4445 X1 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq4445
    | exact resolve eq4445 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4445
  have eq13710 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X1 (σ (k X0 X0))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq6426 X1 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq6426
    | exact resolve eq6426 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6426
  have eq20017 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op X0 (σ (M.op (M.op x y) x))) y) := by
    intro X0
    first
    | (have i₁ := eq12870 (k x x) X0
       have i₂ := eq485
       grind)
    | exact superpose eq485 eq12870
    | exact resolve eq12870 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12870
  have eq20324 : ∀ X0 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ (M.op (M.op x y) x))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12991 (k x x) X0
       have i₂ := eq485
       grind)
    | exact superpose eq485 eq12991
    | exact resolve eq12991 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq20338 : ∀ X0 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (k (σ (k X0 X0)) (σ (k X0 X0))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12991 X0 (σ (k X0 X0))
       have i₂ := eq174 (σ (k X0 X0))
       grind)
    | exact superpose eq174 eq12991
    | exact resolve eq12991 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12991
  have eq20457 : ∀ X0 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ (k (k X0 X0) (k X0 X0))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq20338 X0
       have i₂ := eq10 (k X0 X0) (k X0 X0)
       grind)
    | exact superpose eq10 eq20338
    | exact resolve eq20338 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20338
  have eq20471 : ∀ X0 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq20457 X0
       have i₂ := eq3369 X0
       grind)
    | exact superpose eq3369 eq20457
    | exact resolve eq20457 eq3369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3369 eq20457
  have eq20472 : ∀ X0 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ (M.op (k (M.op x y) (M.op x y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq7168 eq20471
    | exact resolve eq20471 eq7168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7168 eq20471
  have eq20905 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 (σ (M.op (M.op (σ x) (σ y)) (σ x)))) (σ x)) := by
    intro X0
    first
    | exact superpose eq532 eq13710
    | exact resolve eq13710 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13710
  have eq23338 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (k (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) (σ y)) := by
    first
    | (have i₁ := eq20324 (σ (M.op sF0 x))
       have i₂ := eq174 (σ (M.op sF0 x))
       grind)
    | exact superpose eq174 eq20324
    | exact resolve eq20324 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20324
  have eq23459 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ (k (M.op (M.op x y) x) (M.op (M.op x y) x))) (σ y)) := by
    first
    | (have i₁ := eq23338
       have i₂ := eq10 (M.op sF0 x) (M.op sF0 x)
       grind)
    | exact superpose eq10 eq23338
    | exact resolve eq23338 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23338
  have eq23465 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ (M.op (M.op x y) x)) (σ y)) := by
    first
    | (have i₁ := eq23459
       have i₂ := eq309 sF0
       grind)
    | exact superpose eq309 eq23459
    | exact resolve eq23459 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309 eq23459
  have eq23775 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ (k (M.op x y) (M.op x y))) (σ y)) := by
    first
    | exact superpose eq221 eq20472
    | exact resolve eq20472 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20472
  have eq23847 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq41 eq23775
    | exact resolve eq23775 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23775
  have eq23879 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq20 eq23847
    | exact resolve eq23847 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23847
  have eq28005 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (k (σ (M.op (M.op (σ x) (σ y)) (σ x))) (σ (M.op (M.op (σ x) (σ y)) (σ x)))) (σ x)) := by
    first
    | (have i₁ := eq20905 (σ (M.op sF4 sF2))
       have i₂ := eq174 (σ (M.op sF4 sF2))
       grind)
    | exact superpose eq174 eq20905
    | exact resolve eq20905 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20905
  have eq28111 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ (k (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (σ x)))) (σ x)) := by
    first
    | (have i₁ := eq28005
       have i₂ := eq10 (M.op sF4 sF2) (M.op sF4 sF2)
       grind)
    | exact superpose eq10 eq28005
    | exact resolve eq28005 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28005
  have eq28114 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ (M.op (M.op (σ x) (σ y)) (σ x))) (σ x)) := by
    first
    | exact superpose eq326 eq28111
    | exact resolve eq28111 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28111
  have eq45519 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq12227 eq822
    | exact resolve eq822 eq12227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq45531 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq45519
       have r₂ := eq27
       grind)
    | exact resolve eq45519 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45519
  have eq45540 : (k (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq45531 eq326
    | exact resolve eq326 eq45531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq45541 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq45531 eq184
    | exact resolve eq184 eq45531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45543 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq45531 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq45531
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq45531
       grind)
    | exact resolve eq12 eq45531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45598 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq45543
  have eq45599 : (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq45598
  have eq45636 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq45599
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq45599
    | exact resolve eq45599 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45599
  have eq45654 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq12227 eq45636
    | exact resolve eq45636 eq12227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12227 eq45636
  have eq45658 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq45654 eq532
    | exact resolve eq532 eq45654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq45661 : (τ (σ (M.op x y))) = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq45654 eq97
    | exact resolve eq97 eq45654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq45723 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq28 eq45661
    | exact resolve eq45661 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45661
  have eq45725 : (k (σ x) (σ x)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq45540 eq45658
    | exact resolve eq45658 eq45540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45658
  have eq45738 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq45654 eq45725
    | exact resolve eq45725 eq45654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45725
  have eq46206 : (τ (σ (M.op x y))) = (k (τ (σ (M.op x y))) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq45738 eq163
    | exact resolve eq163 eq45738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq45738
  have eq46260 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq28 eq46206
    | exact resolve eq46206 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq46206
  have eq50100 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq46260 eq3808
    | exact resolve eq3808 eq46260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3808 eq46260
  have eq51148 : (k (σ x) (σ x)) = (M.op (σ (k (σ x) (σ x))) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq45540 eq28114
    | exact resolve eq28114 eq45540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28114
  have eq51233 : (σ (M.op x y)) = (M.op (σ (σ (M.op x y))) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq45654 eq51148
    | exact resolve eq51148 eq45654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51148
  have eq51585 : ∀ X0 X1 : G, (M.op X1 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq45541 eq45541
    | exact resolve eq45541 eq45541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51652 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq45541 eq45540
    | exact resolve eq45540 eq45541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51811 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq45541 eq51233
    | exact resolve eq51233 eq45541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45541 eq51233
  have eq51847 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq51811
  have eq51848 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq51652 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51652
  have eq51851 : ∀ X0 X1 : G, (M.op X1 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq51585 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51585
  have eq51886 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq45654 eq51848
    | exact resolve eq51848 eq45654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51848
  have eq52195 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq51886 eq45531
    | exact resolve eq45531 eq51886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51886
  have eq52229 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq52195
  have eq52442 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq232 x
       have i₂ := eq52229
       grind)
    | exact superpose eq52229 eq232
    | exact resolve eq232 eq52229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52229
  have eq52546 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq52442
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52442
    | exact resolve eq52442 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52442
  have eq72392 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq51851 eq45531
    | exact resolve eq45531 eq51851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45531
  have eq72434 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq72392 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72392
  have eq73162 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq72434 eq45540
    | exact resolve eq45540 eq72434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72434
  have eq73173 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq73162
  have eq73430 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq73173 eq141
    | exact resolve eq141 eq73173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq73173
  have eq73484 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq29 eq73430
    | exact resolve eq73430 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73430
  have eq73492 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq45723 eq73484
    | exact resolve eq73484 eq45723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45723 eq73484
  have eq73500 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq232 x
       have i₂ := eq73492
       grind)
    | exact superpose eq73492 eq232
    | exact resolve eq232 eq73492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq73505 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq183 X0 y
       have i₂ := eq73492
       grind)
    | exact superpose eq73492 eq183
    | exact resolve eq183 eq73492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq73610 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq73500
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq73500
    | exact resolve eq73500 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73500
  have eq73657 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq73610 eq41
    | exact resolve eq41 eq73610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73721 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq73657
    | exact resolve eq73657 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73657
  have eq73890 : (M.op (k (M.op x y) (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq73721 eq5953
    | exact resolve eq5953 eq73721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73931 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (k (M.op x y) (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq73890
       have i₂ := eq174 sF1
       grind)
    | exact superpose eq174 eq73890
    | exact resolve eq73890 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73890
  have eq73947 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq73610 eq73931
    | exact resolve eq73931 eq73610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73931
  have eq73950 : (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq73721 eq73947
    | exact resolve eq73947 eq73721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73947
  have eq74126 : ∀ X0 X1 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (M.op X1 (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq73950 eq2638
    | exact resolve eq2638 eq73950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2638 eq73950
  have eq74171 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op X0 (M.op X1 (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq73721 eq74126
    | exact resolve eq74126 eq73721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73721 eq74126
  have eq75140 : x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq73492
       have i₂ := eq73505 y
       grind)
    | exact superpose eq73505 eq73492
    | exact resolve eq73492 eq73505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73492 eq73505
  have eq75153 : x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq75140
  have eq75304 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op X0 (σ x)) y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq75153 eq20017
    | exact resolve eq20017 eq75153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20017
  have eq75314 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq75153 eq23465
    | exact resolve eq23465 eq75153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23465 eq75153
  have eq75445 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq75314
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq75314
    | exact resolve eq75314 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75314
  have eq75452 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op X0 (σ x)) y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq75304 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq75304
    | (have j0 := eq75304 X0
       grind)
    | exact resolve eq75304 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75304
  have eq75469 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq75445
    | exact resolve eq75445 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75445
  have eq75472 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (σ x)) y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq73610 eq75452
    | exact resolve eq75452 eq73610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73610 eq75452
  have eq97448 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (σ x)) y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq51851 eq50100
    | exact resolve eq50100 eq51851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50100 eq51851
  have eq97569 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (σ x)) y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq97448 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97448
  have eq97665 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (σ x)) y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq75472 eq97569
    | (have j0 := eq97569 X0
       have j1 := eq75472 X0
       grind)
    | exact resolve eq97569 eq75472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75472 eq97569
  have eq97732 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op X0 (σ x)) y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq221 eq97665
    | (have j0 := eq97665 X0
       grind)
    | exact resolve eq97665 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97665
  have eq100676 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op X2 (σ x)))) = (M.op X3 (M.op X4 (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq51847 eq2519
    | exact resolve eq2519 eq51847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2519 eq51847
  have eq101488 : ∀ X3 X4 : G, (M.op (k (σ x) (σ x)) (σ x)) = (M.op X3 (M.op X4 (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X3 X4
    first
    | (have i₁ := eq100676 x x X3 X3 X4
       have i₂ := eq2955 sF2 x x X3
       grind)
    | exact superpose eq2955 eq100676
    | exact resolve eq100676 eq2955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2955 eq100676
  have eq102278 : ∀ X3 X4 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op X3 (M.op X4 (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X3 X4
    first
    | exact superpose eq544 eq101488
    | exact resolve eq101488 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544 eq101488
  have eq102890 : ∀ X3 X4 : G, (k (σ x) (σ x)) = (M.op X3 (M.op X4 (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X3 X4
    first
    | exact superpose eq45540 eq102278
    | exact resolve eq102278 eq45540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45540 eq102278
  have eq103231 : ∀ X3 X4 : G, (σ (M.op x y)) = (M.op X3 (M.op X4 (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X3 X4
    first
    | exact superpose eq45654 eq102890
    | exact resolve eq102890 eq45654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45654 eq102890
  have eq103274 : ∀ X3 X4 : G, (σ (M.op x y)) = (M.op X3 (M.op X4 (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ x = y := by
    intro X3 X4
    first
    | exact superpose eq74171 eq103231
    | (have j0 := eq103231 X3 X4
       have j1 := eq74171 X3 X4
       grind)
    | exact resolve eq103231 eq74171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74171 eq103231
  have eq103300 : ∀ X3 X4 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op X3 (M.op X4 (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X3 X4
    first
    | exact superpose eq221 eq103274
    | (have j0 := eq103274 X3 X4
       grind)
    | exact resolve eq103274 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq103274
  have eq103324 : ∀ X3 X4 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op X3 (M.op X4 (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X3 X4
    first
    | exact superpose eq52546 eq103300
    | exact resolve eq103300 eq52546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52546 eq103300
  have eq103340 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq184 eq103324
    | exact resolve eq103324 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq103324
  have eq103468 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op X0 (σ x)) y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq103340 eq2649
    | exact resolve eq2649 eq103340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2649 eq103340
  have eq103531 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq97732 eq103468
    | exact resolve eq103468 eq97732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97732 eq103468
  have eq103532 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq103531
  have eq103589 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op X0 (k X1 X1)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq103532 eq3161
    | exact resolve eq3161 eq103532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3161
  have eq103608 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq103532 eq41
    | exact resolve eq41 eq103532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103678 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq103608
    | exact resolve eq103608 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103608
  have eq103858 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq103678 eq23879
    | exact resolve eq23879 eq103678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23879
  have eq103875 : ∀ X0 X1 : G, (M.op X1 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq103678 eq3211
    | exact resolve eq3211 eq103678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3211
  have eq103878 : (M.op (k (M.op x y) (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq103678 eq5953
    | exact resolve eq5953 eq103678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5953
  have eq103920 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (k (M.op x y) (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq103878
       have i₂ := eq174 sF1
       grind)
    | exact superpose eq174 eq103878
    | exact resolve eq103878 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103878
  have eq103937 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq103532 eq103920
    | exact resolve eq103920 eq103532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103532 eq103920
  have eq103940 : (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq103678 eq103937
    | exact resolve eq103937 eq103678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103937
  have eq106350 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq103875 eq103940
    | exact resolve eq103940 eq103875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103875 eq103940
  have eq106398 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq106350 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106350
  have eq113549 : ∀ X0 X1 : G, (M.op X1 (σ (k X0 X0))) = (M.op (M.op x y) (σ X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq103589 X1 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq103589
    | exact resolve eq103589 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103589
  have eq130142 : ∀ X0 : G, (M.op X0 (σ (k (M.op x y) (M.op x y)))) = (M.op (M.op x y) (σ (k y y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq113549 (k y y) X0
       have i₂ := eq1293
       grind)
    | exact superpose eq1293 eq113549
    | exact resolve eq113549 eq1293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293 eq113549
  have eq130613 : ∀ X0 : G, (M.op X0 (σ (k (M.op x y) (M.op x y)))) = (M.op (M.op x y) (k (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq130142 X0
       have i₂ := eq40 y
       grind)
    | exact superpose eq40 eq130142
    | exact resolve eq130142 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq130142
  have eq130654 : ∀ X0 : G, (M.op X0 (σ (k (M.op x y) (M.op x y)))) = (M.op (M.op x y) (k (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq130613 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq130613
    | (have j0 := eq130613 X0
       grind)
    | exact resolve eq130613 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130613
  have eq130676 : ∀ X0 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op X0 (σ (k (M.op x y) (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq471 eq130654
    | exact resolve eq130654 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471 eq130654
  have eq130688 : ∀ X0 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op X0 (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq41 eq130676
    | exact resolve eq130676 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq130676
  have eq130694 : ∀ X0 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op X0 (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq20 eq130688
    | (have j0 := eq130688 X0
       grind)
    | exact resolve eq130688 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130688
  have eq130699 : ∀ X0 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op X0 (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq103678 eq130694
    | exact resolve eq130694 eq103678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103678 eq130694
  have eq130701 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq106398 eq130699
    | exact resolve eq130699 eq106398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106398 eq130699
  have eq130729 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq130701 eq75469
    | exact resolve eq75469 eq130701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75469
  have eq130782 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq130729
  have eq130825 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq130782
       have r₂ := eq27
       grind)
    | exact resolve eq130782 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130782
  have eq130874 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq130825 eq31
    | exact resolve eq31 eq130825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130825
  have eq130995 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq130874
    | exact resolve eq130874 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130874
  have eq130996 : x = (M.op x y) ∨ x = y := by grind
  clear eq130995
  have eq131006 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq130996
       grind)
    | exact superpose eq130996 eq22
    | exact resolve eq22 eq130996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130996
  have eq131143 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq131006
    | exact resolve eq131006 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131006
  have eq131211 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq131143 eq103858
    | exact resolve eq103858 eq131143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103858 eq131143
  have eq131278 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq131211
  have eq131339 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq131278
    | exact resolve eq131278 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131278
  have eq131372 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq130701 eq131339
    | exact resolve eq131339 eq130701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130701 eq131339
  have eq131378 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq131372
       have r₂ := eq27
       grind)
    | exact resolve eq131372 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131372
  have eq131382 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq131378 eq31
    | exact resolve eq31 eq131378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq131378
  have eq131504 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq131382
    | exact resolve eq131382 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq131382
  have eq131505 : x = y := by grind
  clear eq131504
  have eq131529 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq131505
       grind)
    | exact superpose eq131505 eq18
    | exact resolve eq18 eq131505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq131530 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq131505
       grind)
    | exact superpose eq131505 eq24
    | exact resolve eq24 eq131505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq131505
  have eq131598 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq131530
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq131530
    | exact resolve eq131530 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131530
  have eq131599 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq131529
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq131529
    | exact resolve eq131529 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131529
  have eq131630 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq131598 eq26
    | exact resolve eq26 eq131598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq131598
  have eq131731 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq131630
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq131630
    | exact resolve eq131630 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq131630
  have eq131778 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq131599
       grind)
    | exact superpose eq131599 eq39
    | exact resolve eq39 eq131599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq131599
  have eq131852 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq131778
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq131778
    | exact resolve eq131778 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq131778
  have eq131871 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq131731 eq131852
    | exact resolve eq131852 eq131731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131731 eq131852
  have eq131881 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq131871
    | exact resolve eq131871 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq131871
  have eq131888 : False := by grind
  exact eq131888

/-- `Equation4595`: `(x ◇ x) ◇ x = (y ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_pxx_pxx_pyx_Equation4595 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4595 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4595.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X2) X2) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 (k X0 X1)
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
  clear eq37
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
  have eq177 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op (M.op x y) y) := by
    intro X1 X2
    first
    | (have i₁ := eq16 x X1 X2
       have i₂ := eq177 x
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op (M.op x y) y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X1 X1) X1
       have i₂ := eq177 X1
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op x y) y) X1) := by
    intro X1
    first
    | (have i₁ := eq188 x X1
       have i₂ := eq178 x
       grind)
    | exact superpose eq178 eq188
    | exact resolve eq188 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq193 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq177 x
       have i₂ := eq178 x
       grind)
    | exact superpose eq178 eq177
    | exact resolve eq177 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq196 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X1 X1) X1
       have i₂ := eq178 X1
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) := by
    intro X1
    first
    | (have i₁ := eq196 x X1
       have i₂ := eq178 x
       grind)
    | exact superpose eq178 eq196
    | exact resolve eq196 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq196
  have eq200 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X1) := by
    intro X1
    first
    | exact superpose eq193 eq197
    | exact resolve eq197 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq229 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op x y) y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq189 eq183
    | exact resolve eq183 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq189
  have eq242 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq193 eq229
    | exact resolve eq229 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq445 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq784 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (M.op X0 X0) = (k X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq200 eq28
    | (have j0 := eq28 X0 (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq28 x (M.op (M.op x y) y)
       have r₂ := eq200 x
       grind)
    | exact resolve eq28 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq789 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have j0 := eq784 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq802 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) ≠ X0 ∨ (k X0 (M.op (M.op x y) y)) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq28 X0 X0
       have i₂ := eq789 X0
       grind)
    | exact superpose eq789 eq28
    | exact resolve eq28 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq825 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 X0) ∨ (k X0 (M.op (M.op x y) y)) = X0 ∨ (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq789 X0
       grind)
    | exact superpose eq789 eq11
    | exact resolve eq11 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq831 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq832 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq879 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 X0) ∨ (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have j0 := eq825 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq903 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq879 X0
       have j1 := eq802 X0
       grind)
    | (have r₁ := eq879 X0
       have r₂ := eq802 X0
       grind)
    | exact resolve eq879 eq802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802 eq879
  have eq923 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq789 (M.op sF0 y)
       have i₂ := eq903 (M.op sF0 y)
       grind)
    | exact superpose eq903 eq789
    | exact resolve eq789 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq935 : ∀ X0 : G, (τ (k (σ X0) (M.op (M.op x y) y))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq445 X0 (σ X0)
       have i₂ := eq903 (σ X0)
       grind)
    | (have i₁ := eq445 X0 (M.op (M.op x y) y)
       have i₂ := eq903 (σ X0)
       grind)
    | exact superpose eq903 eq445
    | exact resolve eq445 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq939 : ∀ X0 : G, (k X0 X0) = (τ (k (σ X0) (M.op (M.op x y) y))) := by
    intro X0
    first
    | (have i₁ := eq935 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq935
    | exact resolve eq935 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq952 : ∀ X0 : G, (k X0 X0) = (k X0 (τ (M.op (M.op x y) y))) := by
    intro X0
    first
    | (have i₁ := eq939 X0
       have i₂ := eq445 X0 (M.op sF0 y)
       grind)
    | exact superpose eq445 eq939
    | exact resolve eq939 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939
  have eq989 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq186 X0 X0
       have i₂ := eq923 X0
       grind)
    | exact superpose eq923 eq186
    | exact resolve eq186 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq1045 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq989 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq989
    | exact resolve eq989 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1958 : (M.op (M.op x y) y) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq242 eq1045
    | exact resolve eq1045 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2024 : (M.op (M.op x y) y) = (k (σ (M.op (M.op x y) y)) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq1958
       have i₂ := eq789 (σ (M.op sF0 y))
       grind)
    | exact superpose eq789 eq1958
    | exact resolve eq1958 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789 eq1958
  have eq3337 : (τ (M.op (M.op x y) y)) = (k (M.op (M.op x y) y) (τ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq2024 eq445
    | exact resolve eq445 eq2024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445 eq2024
  have eq3344 : (k (M.op (M.op x y) y) (M.op (M.op x y) y)) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq952 eq3337
    | exact resolve eq3337 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952 eq3337
  have eq3347 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq242 eq3344
    | exact resolve eq3344 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242 eq3344
  have eq3364 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq3347 eq14
    | exact resolve eq14 eq3347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3748 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq831
       grind)
    | exact superpose eq831 eq40
    | exact resolve eq40 eq831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq831
  have eq3750 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3748
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3748
    | exact resolve eq3748 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3748
  have eq3752 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq3750
    | exact resolve eq3750 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3750
  have eq3754 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3752
       have i₂ := eq923 y
       grind)
    | exact superpose eq923 eq3752
    | exact resolve eq3752 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3752
  have eq3766 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3754 eq832
    | exact resolve eq832 eq3754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832 eq3754
  have eq3775 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3766
       have r₂ := eq27
       grind)
    | exact resolve eq3766 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3766
  have eq3779 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3775
       have i₂ := eq923 sF3
       grind)
    | exact superpose eq923 eq3775
    | exact resolve eq3775 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923 eq3775
  have eq3781 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3779 eq116
    | exact resolve eq116 eq3779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq3779
  have eq3797 : x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq3781
    | exact resolve eq3781 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3781
  have eq3798 : x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3797
  have eq3810 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq989 y
       have i₂ := eq3798
       grind)
    | exact superpose eq3798 eq989
    | exact resolve eq989 eq3798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq3811 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1045 y
       have i₂ := eq3798
       grind)
    | exact superpose eq3798 eq1045
    | exact resolve eq1045 eq3798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045 eq3798
  have eq3815 : (M.op (M.op x y) y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3811
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3811
    | exact resolve eq3811 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3811
  have eq3816 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3810
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3810
    | exact resolve eq3810 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3810
  have eq3820 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3815
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3815
    | exact resolve eq3815 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3815
  have eq3824 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq3820
    | exact resolve eq3820 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3820
  have eq3825 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3816 eq3824
    | exact resolve eq3824 eq3816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3824
  have eq3827 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3825 eq193
    | exact resolve eq193 eq3825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3829 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  have eq3831 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq3827
    | exact resolve eq3827 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3827
  have eq3833 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3825 eq3831
    | exact resolve eq3831 eq3825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3825 eq3831
  have eq4202 : (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3816 eq3364
    | exact resolve eq3364 eq3816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3816
  have eq4212 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq4202
    | exact resolve eq4202 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4202
  have eq4326 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4212 eq193
    | exact resolve eq193 eq4212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq4329 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq4326
    | exact resolve eq4326 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4326
  have eq4331 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4212 eq4329
    | exact resolve eq4329 eq4212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4329
  have eq4717 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3833 eq200
    | exact resolve eq200 eq3833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4758 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3833 eq3347
    | exact resolve eq3347 eq3833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3833
  have eq4778 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq4758
    | exact resolve eq4758 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4758
  have eq4904 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4778 eq27
    | exact resolve eq27 eq4778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4778
  have eq5180 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4331 eq3347
    | exact resolve eq3347 eq4331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3347 eq4331
  have eq5201 : x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq5180
    | exact resolve eq5180 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq5180
  have eq5240 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq5201
       have r₂ := eq4904
       grind)
    | exact resolve eq5201 eq4904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4904 eq5201
  have eq5279 : (M.op x y) = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq5240
       grind)
    | exact superpose eq5240 eq18
    | exact resolve eq18 eq5240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5291 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) := by grind
  clear eq5240
  have eq5352 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5279 eq4717
    | exact resolve eq4717 eq5279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4717 eq5279
  have eq5359 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq5352
  have eq5366 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq5359
       have r₂ := eq3829
       grind)
    | exact resolve eq5359 eq3829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3829 eq5359
  have eq5374 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5366 eq27
    | exact resolve eq27 eq5366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5377 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5366 eq4212
    | exact resolve eq4212 eq5366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4212 eq5366
  have eq5378 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq5377
  have eq5381 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq5378
       have r₂ := eq5291
       grind)
    | exact resolve eq5378 eq5291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5291 eq5378
  have eq5383 : x = (M.op x y) := by
    first
    | (have r₁ := eq5381
       have r₂ := eq5374
       grind)
    | exact resolve eq5381 eq5374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5374 eq5381
  have eq5386 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq5383
       grind)
    | exact superpose eq5383 eq18
    | exact resolve eq18 eq5383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq5387 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq5383
       grind)
    | exact superpose eq5383 eq22
    | exact resolve eq22 eq5383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5383
  have eq5805 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq5386 eq200
    | exact resolve eq200 eq5386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq5847 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq5386 eq3364
    | exact resolve eq3364 eq5386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3364 eq5386
  have eq5955 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq5847 eq5387
    | exact resolve eq5387 eq5847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5387
  have eq5956 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq5847 eq20
    | exact resolve eq20 eq5847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5847
  have eq6026 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq5955 eq26
    | exact resolve eq26 eq5955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq5955
  have eq6074 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5805 eq6026
    | exact resolve eq6026 eq5805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5805 eq6026
  have eq6147 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq6074 eq27
    | exact resolve eq27 eq6074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq6074
  have eq6153 : False := by grind
  exact eq6153

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_pyy_pxx_pyy_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq174 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq174 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq5922 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq195 X0 X1
       have j1 := eq193 X1 X0
       grind)
    | (have r₁ := eq195 X0 X1
       have r₂ := eq193 X0 X1
       grind)
    | (have r₁ := eq195 X1 X0
       have r₂ := eq193 X0 X1
       grind)
    | (have r₁ := eq195 X1 X1
       have r₂ := eq193 X1 X1
       grind)
    | exact resolve eq195 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq195
  have eq6879 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq5922 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5922
  have eq6894 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq6879 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq6879 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq6879 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq6879 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq6879 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6879
  have eq7128 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq6894 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq6894 X0 X1
       grind)
    | exact superpose eq6894 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq6894 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq6894 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq6894 X0 X0
       grind)
    | exact resolve eq12 eq6894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7231 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq7128 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7128
  have eq7431 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq7231 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7231
  have eq7438 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq7431 X0 X1
       have j1 := eq6894 X0 X1
       grind)
    | (have r₁ := eq7431 X0 X1
       have r₂ := eq6894 X0 X1
       grind)
    | (have r₁ := eq7431 X0 X0
       have r₂ := eq6894 X0 X0
       grind)
    | exact resolve eq7431 eq6894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6894 eq7431
  have eq7454 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq7438 (σ X0) (σ X1)
       grind)
    | exact superpose eq7438 eq15
    | exact resolve eq15 eq7438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7465 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7454 X0 X1
       have i₂ := eq7438 X0 X1
       grind)
    | exact superpose eq7438 eq7454
    | exact resolve eq7454 eq7438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7438 eq7454
  have eq7632 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7465 y x
       grind)
    | exact superpose eq7465 eq16
    | (have r₁ := eq16
       have r₂ := eq7465 y x
       grind)
    | exact resolve eq16 eq7465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7465
  have eq7668 : False := by grind
  exact eq7668

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyx_y_pxy_y_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X1 X2) X0) := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X0 X3
       have i₂ := eq14 X2 X0 X1
       grind)
    | (have i₁ := eq14 X2 X0 X2
       have i₂ := eq14 X0 X2 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (M.op X0 X0) x) = (M.op (M.op x y) X0) := by
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
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op X2 X2) X0
       have i₂ := eq14 X2 X0 X1
       grind)
    | (have i₁ := eq14 X0 (M.op X1 X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq71 (σ X0)
       grind)
    | exact superpose eq71 eq10
    | exact resolve eq10 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq73
    | exact resolve eq73 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq83 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq107 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq24 eq36
  have eq111 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq107
       have i₂ := eq71 sF3
       grind)
    | exact superpose eq71 eq107
    | exact resolve eq107 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq113 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq111
       have i₂ := eq71 y
       grind)
    | exact superpose eq71 eq111
    | exact resolve eq111 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq111
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq106
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq106
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq106 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq121
    | exact resolve eq121 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq123 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq122
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq122
    | exact resolve eq122 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq124 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq123
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq123
    | exact resolve eq123 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq245 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1
       have i₂ := eq14 X1 x X0
       grind)
    | (have i₁ := eq53 x
       have i₂ := eq14 x x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op X2 X2) X4) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq51 (M.op X2 X2) X0 X3 X4
       have i₂ := eq14 X2 X0 X1
       grind)
    | (have i₁ := eq51 (M.op X1 X2) X0 X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op (M.op X0 X0) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op X0 X0) x X1 X2
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq645 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = (M.op (M.op (M.op X3 X4) X2) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X3 X4 X2 X0
       have i₂ := eq51 X0 X0 (M.op X2 X2) X1
       grind)
    | (have i₁ := eq55 X3 X4 X2 X0
       have i₂ := eq51 X0 X1 (M.op X2 X2) X0
       grind)
    | exact superpose eq51 eq55
    | exact resolve eq55 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq55
  have eq1719 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq78 (M.op y y)
       have i₂ := eq113
       grind)
    | exact superpose eq113 eq78
    | exact resolve eq78 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq113
  have eq9979 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op x y) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq419 X0 X1 X2 X3 x
       have i₂ := eq423 X2 X3 x
       grind)
    | exact superpose eq423 eq419
    | exact resolve eq419 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419 eq423
  have eq13141 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = (M.op (M.op (M.op x y) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq645 X0 X1 X2 x x
       have i₂ := eq9979 x x X2 X0
       grind)
    | (have i₁ := eq645 x X1 X2 x y
       have i₂ := eq9979 X0 X1 X2 x
       grind)
    | exact superpose eq9979 eq645
    | (have j0 := eq645 X0 X1 X2 x y
       grind)
    | exact resolve eq645 eq9979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645 eq9979
  have eq44646 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq124 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44647 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq44646
    | exact resolve eq44646 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44646
  have eq44658 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq44647
       have r₂ := eq27
       grind)
    | exact resolve eq44647 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44647
  have eq44662 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq44658
    | exact resolve eq44658 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44658
  have eq44664 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq44662
    | exact resolve eq44662 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44662
  have eq44670 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq44664 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq44664
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq44664
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq44664
       grind)
    | exact resolve eq13 eq44664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44664
  have eq44773 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq44670
       have r₂ := eq26
       grind)
    | exact resolve eq44670 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44670
  have eq44811 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq44773 eq124
    | exact resolve eq124 eq44773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44773
  have eq44819 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq44811
  have eq44821 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq44819
       have r₂ := eq27
       grind)
    | exact resolve eq44819 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44819
  have eq45197 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq44821
       grind)
    | exact superpose eq44821 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq44821
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq44821
       grind)
    | exact resolve eq13 eq44821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45275 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq45197
       have r₂ := eq18
       grind)
    | exact resolve eq45197 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45197
  have eq45294 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq106
       have i₂ := eq45275
       grind)
    | exact superpose eq45275 eq106
    | exact resolve eq106 eq45275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45275
  have eq45308 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq45294
    | exact resolve eq45294 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45294
  have eq45344 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45308 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq45308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45347 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq45344
    | exact resolve eq45344 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45344
  have eq45358 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq45347
       have r₂ := eq27
       grind)
    | exact resolve eq45347 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45347
  have eq45362 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq45358
    | exact resolve eq45358 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45358
  have eq45363 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq45362
  have eq45366 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq45363
    | exact resolve eq45363 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45363
  have eq45766 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45366 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq45366
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq45366
       grind)
    | exact resolve eq13 eq45366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45366
  have eq45869 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq45766
       have r₂ := eq26
       grind)
    | exact resolve eq45766 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45766
  have eq45915 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45869 eq45308
    | exact resolve eq45308 eq45869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45308 eq45869
  have eq45917 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq45915
  have eq45921 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq45917
       have r₂ := eq27
       grind)
    | exact resolve eq45917 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45917
  have eq45925 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45921 eq27
    | exact resolve eq27 eq45921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45926 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45921 eq83
    | (have r₁ := eq83
       have r₂ := eq45921
       grind)
    | exact resolve eq83 eq45921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq45986 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq45926
  have eq115730 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45986 eq124
    | exact resolve eq124 eq45986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115745 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq115730
  have eq115758 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq115745
       have r₂ := eq45925
       grind)
    | exact resolve eq115745 eq45925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115745
  have eq121901 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115758 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq115758
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq115758
       grind)
    | exact resolve eq13 eq115758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115758
  have eq122016 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq121901
    | exact resolve eq121901 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121901
  have eq122025 : (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq122016
       have r₂ := eq44821
       grind)
    | exact resolve eq122016 eq44821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44821 eq122016
  have eq172315 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122025 eq124
    | exact resolve eq124 eq122025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq122025
  have eq172332 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq172315
  have eq172345 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq172332
       have r₂ := eq45925
       grind)
    | exact resolve eq172332 eq45925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172332
  have eq172355 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq172345
       grind)
    | exact superpose eq172345 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq172345
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq172345
       grind)
    | exact resolve eq13 eq172345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172345
  have eq172471 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq172355
       have r₂ := eq18
       grind)
    | exact resolve eq172355 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172355
  have eq172491 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq106
       have i₂ := eq172471
       grind)
    | exact superpose eq172471 eq106
    | exact resolve eq106 eq172471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq172471
  have eq172511 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq172491
    | exact resolve eq172491 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172491
  have eq172559 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq172511 eq45986
    | exact resolve eq45986 eq172511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45986
  have eq172564 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq172559
  have eq172572 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq172564
       have r₂ := eq45925
       grind)
    | exact resolve eq172564 eq45925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172564
  have eq172621 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq172572 eq13
    | exact resolve eq13 eq172572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172572
  have eq172747 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq172621
    | exact resolve eq172621 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172621
  have eq172757 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq172747
       have r₂ := eq45921
       grind)
    | exact resolve eq172747 eq45921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45921 eq172747
  have eq172778 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq172757 eq172511
    | exact resolve eq172511 eq172757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172511 eq172757
  have eq172783 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq172778
  have eq172795 : x = (M.op x y) := by
    first
    | (have r₁ := eq172783
       have r₂ := eq45925
       grind)
    | exact resolve eq172783 eq45925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45925 eq172783
  have eq172811 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq172795 eq20
    | exact resolve eq20 eq172795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173128 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq172811
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq172811
    | exact resolve eq172811 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq172811
  have eq173338 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq173128 eq26
    | exact resolve eq26 eq173128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq173128
  have eq176314 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (M.op x y) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq1719
       have i₂ := eq13141 sF3 sF3 sF3
       grind)
    | exact superpose eq13141 eq1719
    | exact resolve eq1719 eq13141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719
  have eq176315 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op x (σ y)) (σ y)) := by
    first
    | exact superpose eq172795 eq176314
    | exact resolve eq176314 eq172795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176314
  have eq176316 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op x y) (σ y)) := by
    first
    | (have i₁ := eq176315
       have i₂ := eq245 sF3 sF3
       grind)
    | exact superpose eq245 eq176315
    | exact resolve eq176315 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176315
  have eq176317 : (σ (M.op (M.op y y) (M.op y y))) = (M.op x (σ y)) := by
    first
    | exact superpose eq172795 eq176316
    | exact resolve eq176316 eq172795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176316
  have eq176318 : (σ (M.op (M.op (M.op x y) y) y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq176317
       have i₂ := eq13141 y y y
       grind)
    | exact superpose eq13141 eq176317
    | exact resolve eq176317 eq13141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13141 eq176317
  have eq176319 : (σ (M.op (M.op y y) (M.op x y))) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq176318
       have i₂ := eq14 y sF0 y
       grind)
    | exact superpose eq14 eq176318
    | exact resolve eq176318 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176318
  have eq176320 : (σ (M.op (M.op y y) x)) = (M.op x (σ y)) := by
    first
    | exact superpose eq172795 eq176319
    | exact resolve eq176319 eq172795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176319
  have eq176321 : (σ (M.op (M.op x x) y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq176320
       have i₂ := eq14 x y y
       grind)
    | (have i₁ := eq176320
       have i₂ := eq14 y x x
       grind)
    | exact superpose eq14 eq176320
    | exact resolve eq176320 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176320
  have eq176322 : (σ (M.op (M.op x y) y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq176321
       have i₂ := eq245 x y
       grind)
    | exact superpose eq245 eq176321
    | exact resolve eq176321 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176321
  have eq176323 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq172795 eq176322
    | exact resolve eq176322 eq172795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176322
  have eq176324 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq176323
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq176323
    | exact resolve eq176323 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq176323
  have eq176325 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq20 eq176324
    | exact resolve eq176324 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq176324
  have eq176326 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq176325 eq245
    | exact resolve eq245 eq176325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq176505 : ∀ X0 : G, (M.op x X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq172795 eq176326
    | exact resolve eq176326 eq172795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172795 eq176326
  have eq176951 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq176505 eq173338
    | exact resolve eq173338 eq176505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173338 eq176505
  have eq177260 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq176325 eq176951
    | exact resolve eq176951 eq176325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176325 eq176951
  have eq177393 : False := by grind
  exact eq177393

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pyx_x_pyx_x_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq81 : y ≠ (M.op x y) ∨ (M.op x x) = (M.op y x) ∨ y = (k y x) := by
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
  have eq82 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
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
  have eq96 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq113 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq90
    | (have j0 := eq90 (σ X0) (σ X1)
       grind)
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq90 y x
       grind)
    | exact superpose eq90 eq96
    | (have j1 := eq90 y x
       grind)
    | exact resolve eq96 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq128 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq120
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq120
    | exact resolve eq120 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq130 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq128
    | exact resolve eq128 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq131 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq130
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq130
    | exact resolve eq130 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq200 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq131 eq90
    | (have j0 := eq90 (σ y) (σ x)
       grind)
    | exact resolve eq90 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq201 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq200
    | exact resolve eq200 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq204 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq201
       have r₂ := eq27
       grind)
    | exact resolve eq201 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq206 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq204
    | exact resolve eq204 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq208 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq206 eq27
    | exact resolve eq27 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq845 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq206 eq82
    | (have r₁ := eq82
       have r₂ := eq206
       grind)
    | exact resolve eq82 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq206
  have eq846 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq845
  have eq1213 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq113 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq79999 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq846 eq13
    | (have j0 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq846
       grind)
    | exact resolve eq13 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq80087 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq79999
  have eq80133 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq80087
    | exact resolve eq80087 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80087
  have eq80162 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq131 eq80133
    | exact resolve eq80133 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq80133
  have eq80176 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq80162
  have eq80179 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq80176
       have r₂ := eq208
       grind)
    | exact resolve eq80176 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq80176
  have eq80180 : y = (M.op x y) := by
    first
    | (have r₁ := eq80179
       have r₂ := eq27
       grind)
    | exact resolve eq80179 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80179
  have eq80181 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq80180 eq20
    | exact resolve eq20 eq80180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq80183 : y ≠ y ∨ (M.op x x) = (M.op y x) ∨ y = (k y x) := by
    first
    | exact superpose eq80180 eq81
    | (have r₁ := eq81
       have r₂ := eq80180
       grind)
    | exact resolve eq81 eq80180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq80218 : (M.op x x) = (M.op y x) ∨ y = (k y x) := by grind
  clear eq80183
  have eq80232 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq80181
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq80181
    | exact resolve eq80181 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80181
  have eq80238 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq80232 eq26
    | exact resolve eq26 eq80232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq93552 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq80218
       grind)
    | exact superpose eq80218 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq80218
       grind)
    | exact resolve eq13 eq80218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80218
  have eq93609 : (M.op x y) = (k y x) ∨ y = (k y x) := by grind
  clear eq93552
  have eq93639 : (M.op x y) = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq93609
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq93609
    | exact resolve eq93609 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq93609
  have eq93675 : y = (k y x) ∨ y = (k y x) := by
    first
    | exact superpose eq80180 eq93639
    | exact resolve eq93639 eq80180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80180 eq93639
  have eq93676 : y = (k y x) := by grind
  clear eq93675
  have eq94052 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1213 x y
       have i₂ := eq93676
       grind)
    | exact superpose eq93676 eq1213
    | (have j0 := eq1213 x y
       grind)
    | exact resolve eq1213 eq93676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213 eq93676
  have eq94058 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq94052
  have eq94068 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq94058
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq94058
    | exact resolve eq94058 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq94058
  have eq94078 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq80232 eq94068
    | exact resolve eq94068 eq80232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80232 eq94068
  have eq94086 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq94078
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq94078
    | exact resolve eq94078 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq94078
  have eq94094 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq80238 eq94086
    | exact resolve eq94086 eq80238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80238 eq94086
  have eq94101 : False := by grind
  exact eq94101
