import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation508`: `x = y ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_pxy_pyx_Equation508 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law508 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law508.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9
    | exact resolve eq9 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X0 (M.op X2 X2)) X1 (M.op X0 (M.op X2 X2))
       have i₂ := eq8 X0 (M.op X0 (M.op X2 X2)) X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X1 (M.op X0 X0)
       have i₂ := eq8 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0 X1 x
       have i₂ := eq22 x X0
       grind)
    | exact superpose eq22 eq21
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq27 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1) X0 X1
       have i₂ := eq22 (M.op X1 X1) X0
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X2
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X1
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq47 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq39 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq80 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X1 X1
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq88 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20
    | exact resolve eq20 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq111 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq150 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 X1) ∨ (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 (σ X0) X1
       have i₂ := eq45 X2 X0
       grind)
    | exact superpose eq45 eq27
    | (have j1 := eq45 X2 X0
       grind)
    | exact resolve eq27 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (σ X0) X1
       have i₂ := eq45 X2 X0
       grind)
    | exact superpose eq45 eq22
    | (have j1 := eq45 X2 X0
       grind)
    | exact resolve eq22 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq235 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq111 X0 X0
       have i₂ := eq27 X0 X1
       grind)
    | (have i₁ := eq111 X1 X1
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq111
    | (have j0 := eq111 X0 X0
       grind)
    | (have r₁ := eq111 X1 X1
       have r₂ := eq27 X1 X1
       grind)
    | (have r₁ := eq111 X0 X0
       have r₂ := eq27 X0 X0
       grind)
    | exact resolve eq111 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq240 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq111 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq243 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq235 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq357 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq243 X0 (σ X1)
       grind)
    | exact superpose eq243 eq13
    | exact resolve eq13 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X1 X1
       have i₂ := eq243 X0 (τ X1)
       grind)
    | exact superpose eq243 eq88
    | exact resolve eq88 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq360 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X1)
       have i₂ := eq243 X0 (τ X1)
       grind)
    | exact superpose eq243 eq15
    | exact resolve eq15 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq243
  have eq365 : ∀ X0 X1 : G, (k X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq360 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq360
    | exact resolve eq360 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq366 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq359 X0 X1
       have i₂ := eq240 X1
       grind)
    | exact superpose eq240 eq359
    | exact resolve eq359 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq368 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq357 X0 X1
       have i₂ := eq240 X1
       grind)
    | exact superpose eq240 eq357
    | exact resolve eq357 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq590 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (τ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X1 X1
       have i₂ := eq365 X0 (τ X1)
       grind)
    | exact superpose eq365 eq88
    | exact resolve eq88 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq365
  have eq615 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq590 X0 X1
       have i₂ := eq240 X1
       grind)
    | exact superpose eq240 eq590
    | exact resolve eq590 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240 eq590
  have eq644 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq80 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq80
    | (have j0 := eq80 X0 X1
       grind)
    | exact resolve eq80 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq712 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq644 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq644
    | (have j0 := eq644 X0 X1
       grind)
    | exact resolve eq644 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq717 : ∀ X0 X2 : G, (τ (M.op X0 X0)) = (τ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq366 x X2
       have i₂ := eq366 x X0
       grind)
    | exact superpose eq366 eq366
    | exact resolve eq366 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq727 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq366 X1 x
       have i₂ := eq366 x X0
       grind)
    | exact superpose eq366 eq366
    | exact resolve eq366 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X1
       have i₂ := eq366 X1 X0
       grind)
    | exact superpose eq366 eq23
    | exact resolve eq23 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq1399 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq152 y X0 x
       grind)
    | exact superpose eq152 eq14
    | (have j1 := eq152 y X0 x
       grind)
    | exact resolve eq14 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq1973 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (τ (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq615 X1 (τ (M.op X0 X0))
       have i₂ := eq757 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq757 eq615
    | exact resolve eq615 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615 eq757
  have eq2544 : ∀ X0 X2 : G, (τ (M.op X2 X2)) = (τ (τ (τ (M.op X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq717 x X2
       have i₂ := eq727 X0 x
       grind)
    | exact superpose eq727 eq717
    | exact resolve eq717 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717 eq727
  have eq9558 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 X1) ∨ (σ (k X0 X2)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq368 X1 X0
       have i₂ := eq712 X2 X0
       grind)
    | exact superpose eq712 eq368
    | (have j1 := eq712 X2 X0
       grind)
    | exact resolve eq368 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq15671 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq1399 X0
       have i₂ := eq712 x y
       grind)
    | exact superpose eq712 eq1399
    | (have j0 := eq1399 X0
       have j1 := eq712 X0 y
       grind)
    | (have r₁ := eq1399 X0
       have r₂ := eq712 x y
       grind)
    | exact resolve eq1399 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712 eq1399
  have eq15672 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq15671 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15671
  have eq15704 : ∀ X0 : G, (M.op X0 X0) = (τ (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq366 X0 (σ y)
       have i₂ := eq15672 (σ y)
       grind)
    | exact superpose eq15672 eq366
    | exact resolve eq366 eq15672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366 eq15672
  have eq15800 : ∀ X0 : G, (M.op X0 X0) = y ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq15704 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq15704
    | exact resolve eq15704 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15704
  have eq16992 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have j0 := eq15800 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15800
  have eq16993 : y = (M.op y y) := by grind
  clear eq16992
  have eq17467 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq150 y X0 x
       grind)
    | exact superpose eq150 eq14
    | (have j1 := eq150 y X0 x
       grind)
    | exact resolve eq14 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq17653 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq17467 X0
       have j1 := eq9558 y X0 x
       grind)
    | (have r₁ := eq17467 X0
       have r₂ := eq9558 y x x
       grind)
    | exact resolve eq17467 eq9558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9558 eq17467
  have eq17921 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 y X0
       have i₂ := eq16993
       grind)
    | exact superpose eq16993 eq22
    | exact resolve eq22 eq16993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq17951 : ∀ X0 : G, (σ (M.op X0 X0)) = (τ (τ y)) := by
    intro X0
    first
    | (have i₁ := eq1973 y X0
       have i₂ := eq16993
       grind)
    | exact superpose eq16993 eq1973
    | exact resolve eq1973 eq16993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1973
  have eq17959 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (τ (τ y))) := by
    intro X0
    first
    | (have i₁ := eq2544 y X0
       have i₂ := eq16993
       grind)
    | exact superpose eq16993 eq2544
    | exact resolve eq2544 eq16993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2544 eq16993
  have eq17986 : (τ (σ y)) = (τ (τ (τ y))) := by
    first
    | (have i₁ := eq17959 x
       have i₂ := eq17653 x
       grind)
    | exact superpose eq17653 eq17959
    | exact resolve eq17959 eq17653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17959
  have eq17993 : (σ (σ y)) = (τ (τ y)) := by
    first
    | (have i₁ := eq17951 x
       have i₂ := eq17653 x
       grind)
    | exact superpose eq17653 eq17951
    | exact resolve eq17951 eq17653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17653 eq17951
  have eq18008 : y = (τ (τ (τ y))) := by
    first
    | (have i₁ := eq17986
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq17986
    | exact resolve eq17986 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17986
  have eq18017 : y = (τ (σ (σ y))) := by
    first
    | (have i₁ := eq18008
       have i₂ := eq17993
       grind)
    | exact superpose eq17993 eq18008
    | exact resolve eq18008 eq17993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17993 eq18008
  have eq18021 : y = (σ y) := by
    first
    | (have i₁ := eq18017
       have i₂ := eq9 (σ y)
       grind)
    | exact superpose eq9 eq18017
    | exact resolve eq18017 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18017
  have eq18928 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq18021
       grind)
    | exact superpose eq18021 eq14
    | exact resolve eq14 eq18021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18021
  have eq18989 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq18928
       have i₂ := eq17921 (σ x)
       grind)
    | exact superpose eq17921 eq18928
    | exact resolve eq18928 eq17921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18928
  have eq19004 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq18989
       have i₂ := eq17921 x
       grind)
    | exact superpose eq17921 eq18989
    | exact resolve eq18989 eq17921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17921 eq18989
  have eq19005 : False := by grind
  exact eq19005

/-- `Equation508`: `x = y ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation508 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law508 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law508.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq19 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X1 (M.op X0 X0)
       have i₂ := eq8 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1) X0 X1
       have i₂ := eq19 (M.op X1 X1) X0
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X2 X1
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq19 X0 X1
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq73 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq88 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq97 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0)
       have i₂ := eq73 X0 (τ X1)
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X1 (M.op X0 X0)
       have i₂ := eq73 X0 (σ X1)
       grind)
    | exact superpose eq73 eq88
    | exact resolve eq88 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq164 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X0
       have i₂ := eq24 (σ X0) X1
       grind)
    | (have i₁ := eq37 X0 X0
       have i₂ := eq24 X0 (σ X0)
       grind)
    | exact superpose eq24 eq37
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq179 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq37 x y
       grind)
    | exact superpose eq37 eq14
    | (have j1 := eq37 x y
       grind)
    | exact resolve eq14 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq361 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (k X1 (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (σ (M.op X0 X0))
       have i₂ := eq97 X0 (τ X1)
       grind)
    | exact superpose eq97 eq16
    | exact resolve eq16 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq420 : ∀ X0 X1 : G, (τ (τ (M.op X0 X0))) = (k X1 (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X1 (τ (M.op X0 X0))
       have i₂ := eq141 X0 (σ X1)
       grind)
    | exact superpose eq141 eq88
    | exact resolve eq88 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq141
  have eq1017 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq164 X1 (σ (M.op X0 X0))
       have i₂ := eq97 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq97 eq164
    | (have j0 := eq164 X1 (σ (M.op X0 X0))
       grind)
    | exact resolve eq164 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq1018 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (σ (M.op X0 X0)))) ∨ (M.op X1 X1) = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq164 X1 (σ (σ (M.op X0 X0)))
       have i₂ := eq361 X0 (σ (σ (M.op X0 X0)))
       grind)
    | exact superpose eq361 eq164
    | (have j0 := eq164 X1 (σ (σ (M.op X0 X0)))
       grind)
    | exact resolve eq164 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq1020 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) ∨ (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq164 X1 (τ (τ (M.op X0 X0)))
       have i₂ := eq420 X0 (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq420 eq164
    | (have j0 := eq164 X1 (τ (τ (M.op X0 X0)))
       grind)
    | exact resolve eq164 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq420
  have eq1076 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq1020 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1078 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq1018 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018
  have eq1079 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq1017 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017
  have eq1102 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1076 X0 X1
       have i₂ := eq10 (τ (M.op X0 X0))
       grind)
    | exact superpose eq10 eq1076
    | exact resolve eq1076 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq2374 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq179
       have i₂ := eq31 y X0 x
       grind)
    | exact superpose eq31 eq179
    | (have j1 := eq31 y X0 x
       grind)
    | exact resolve eq179 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq179
  have eq2382 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq2374 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2374
  have eq13563 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ y)) ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1102 (σ x) X0
       have i₂ := eq2382 X1
       grind)
    | exact superpose eq2382 eq1102
    | (have j1 := eq2382 X1
       grind)
    | exact resolve eq1102 eq2382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2382
  have eq13621 : ∀ X0 X1 : G, (M.op X0 X0) = y ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13563 X0 X1
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq13563
    | (have j0 := eq13563 X0 X1
       grind)
    | exact resolve eq13563 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13563
  have eq14214 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have j0 := eq13621 y y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13621
  have eq14215 : y = (M.op y y) := by grind
  clear eq14214
  have eq14431 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq19 y X0
       have i₂ := eq14215
       grind)
    | exact superpose eq14215 eq19
    | exact resolve eq19 eq14215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq14443 : ∀ X0 : G, (M.op X0 X0) = (σ (σ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq1078 y X0
       have i₂ := eq14215
       grind)
    | exact superpose eq14215 eq1078
    | exact resolve eq1078 eq14215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078
  have eq14444 : ∀ X0 : G, (M.op X0 X0) = (σ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1079 y X0
       have i₂ := eq14215
       grind)
    | exact superpose eq14215 eq1079
    | exact resolve eq1079 eq14215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079
  have eq14445 : ∀ X0 : G, (M.op X0 X0) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq1102 y X0
       have i₂ := eq14215
       grind)
    | exact superpose eq14215 eq1102
    | exact resolve eq1102 eq14215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102 eq14215
  have eq14480 : (σ (σ y)) = (τ y) := by
    first
    | (have i₁ := eq14444 x
       have i₂ := eq14445 x
       grind)
    | exact superpose eq14445 eq14444
    | exact resolve eq14444 eq14445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14444
  have eq14481 : (σ (σ (σ y))) = (τ y) := by
    first
    | (have i₁ := eq14443 x
       have i₂ := eq14445 x
       grind)
    | exact superpose eq14445 eq14443
    | exact resolve eq14443 eq14445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14443 eq14445
  have eq14485 : (τ y) = (σ (τ y)) := by
    first
    | (have i₁ := eq14481
       have i₂ := eq14480
       grind)
    | exact superpose eq14480 eq14481
    | exact resolve eq14481 eq14480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14480 eq14481
  have eq14486 : y = (τ y) := by
    first
    | (have i₁ := eq14485
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq14485
    | exact resolve eq14485 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14485
  have eq14783 : y = (σ y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq14486
       grind)
    | exact superpose eq14486 eq10
    | exact resolve eq10 eq14486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14486
  have eq15721 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq14783
       grind)
    | exact superpose eq14783 eq14
    | exact resolve eq14 eq14783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14783
  have eq15805 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq15721
       have i₂ := eq14431 (σ x)
       grind)
    | exact superpose eq14431 eq15721
    | exact resolve eq15721 eq14431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15721
  have eq15834 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq15805
       have i₂ := eq14431 x
       grind)
    | exact superpose eq14431 eq15805
    | exact resolve eq15805 eq14431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14431 eq15805
  have eq15835 : False := by grind
  exact eq15835

/-- `Equation52`: `x = x ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation52 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law52 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law52.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq8 (M.op X0 X0) X0
       have i₂ := eq8 X0 (M.op X0 X0)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq22 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq16 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq26 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq33 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq28
    | exact resolve eq28 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq35 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq32
    | exact resolve eq32 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq24
    | exact resolve eq24 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq24 (τ X0) X1
       grind)
    | exact superpose eq24 eq19
    | (have j1 := eq24 (τ X0) X1
       grind)
    | exact resolve eq19 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq24
  have eq63 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq33 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq33
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq92 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq94 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq40 X1 X0
       have i₂ := eq12 (σ X1) X0
       grind)
    | exact superpose eq12 eq40
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq92 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq92
    | exact resolve eq92 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq202 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (σ X1)
       have i₂ := eq26 X0 X1
       grind)
    | exact superpose eq26 eq16
    | (have j1 := eq26 X0 X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq106 X1
       have i₂ := eq26 X0 X1
       grind)
    | exact superpose eq26 eq106
    | (have j1 := eq26 X0 X1
       grind)
    | exact resolve eq106 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq106
  have eq246 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq225 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq225
    | (have j0 := eq225 X0 X1
       grind)
    | exact resolve eq225 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq261 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq40 X1 X0
       have i₂ := eq22 X0 (σ X1)
       grind)
    | exact superpose eq22 eq40
    | (have j1 := eq22 X0 (σ X1)
       grind)
    | exact resolve eq40 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq40
  have eq564 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq35
    | exact resolve eq35 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq637 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq564 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq564
    | (have j0 := eq564 X0 X1
       grind)
    | exact resolve eq564 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq663 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq55
    | exact resolve eq55 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq706 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq663 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq663
    | (have j0 := eq663 X0 X1
       grind)
    | exact resolve eq663 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq760 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1
       have i₂ := eq637 X0 X1
       grind)
    | (have i₁ := eq16 X0
       have i₂ := eq637 (M.op X0 X0) X1
       grind)
    | exact superpose eq637 eq16
    | (have j1 := eq637 X0 X1
       grind)
    | exact resolve eq16 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq961 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (σ X0)
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq16
    | (have j1 := eq52 X0 X0
       grind)
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1439 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq202 x y
       grind)
    | exact superpose eq202 eq14
    | (have j1 := eq202 x y
       grind)
    | exact resolve eq14 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1453 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq202 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq2466 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq63
    | (have j0 := eq63 X1 (σ X0)
       grind)
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq2543 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2466 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2466
    | (have j0 := eq2466 X0 X1
       grind)
    | exact resolve eq2466 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2466
  have eq7100 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq7125 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1453 (τ X1) (τ X0)
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq1453
    | (have j0 := eq1453 (τ X1) (τ X0)
       grind)
    | exact resolve eq1453 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq7159 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7125 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq7125
    | (have j0 := eq7125 X0 X1
       grind)
    | exact resolve eq7125 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7125
  have eq7169 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7159 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq7159
    | (have j0 := eq7159 X0 X1
       grind)
    | exact resolve eq7159 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7159
  have eq7172 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7169 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7169
    | (have j0 := eq7169 X0 X1
       grind)
    | exact resolve eq7169 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7169
  have eq7173 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7172 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7172
    | (have j0 := eq7172 X0 X1
       grind)
    | exact resolve eq7172 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7172
  have eq11179 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq246 x y
       grind)
    | exact superpose eq246 eq14
    | (have j1 := eq246 x y
       grind)
    | exact resolve eq14 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq11218 : y = (k y x) := by
    first
    | (have j1 := eq706 x y
       grind)
    | (have r₁ := eq11179
       have r₂ := eq706 x y
       grind)
    | exact resolve eq11179 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706 eq11179
  have eq11897 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq637 x y
       have i₂ := eq11218
       grind)
    | exact superpose eq11218 eq637
    | (have j0 := eq637 x y
       grind)
    | exact resolve eq637 eq11218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11898 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq760 x y
       have i₂ := eq11218
       grind)
    | exact superpose eq11218 eq760
    | (have j0 := eq760 x y
       grind)
    | exact resolve eq760 eq11218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11899 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1453 x y
       have i₂ := eq11218
       grind)
    | exact superpose eq11218 eq1453
    | (have j0 := eq1453 x y
       grind)
    | exact resolve eq1453 eq11218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1453 eq11218
  have eq17714 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1439
       have i₂ := eq637 x y
       grind)
    | exact superpose eq637 eq1439
    | (have j1 := eq637 x y
       grind)
    | (have r₁ := eq1439
       have r₂ := eq637 x y
       grind)
    | exact resolve eq1439 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq17716 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1439
       have i₂ := eq760 x y
       grind)
    | exact superpose eq760 eq1439
    | (have j1 := eq760 (σ x) (σ y)
       grind)
    | (have r₁ := eq1439
       have r₂ := eq760 x y
       grind)
    | exact resolve eq1439 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760 eq1439
  have eq17720 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17716
  have eq17722 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq17714
  have eq17743 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq17722
       grind)
    | exact superpose eq17722 eq14
    | exact resolve eq14 eq17722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17722
  have eq18124 : (σ x) ≠ (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17743
       have i₂ := eq11897
       grind)
    | exact superpose eq11897 eq17743
    | exact resolve eq17743 eq11897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11897
  have eq18126 : (σ x) ≠ (σ y) ∨ x = (M.op y y) := by grind
  clear eq18124
  have eq18645 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq17720
       grind)
    | exact superpose eq17720 eq14
    | exact resolve eq14 eq17720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18656 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq94 (σ x) y
       have i₂ := eq17720
       grind)
    | exact superpose eq17720 eq94
    | (have j0 := eq94 (σ x) y
       grind)
    | exact resolve eq94 eq17720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq17720
  have eq18678 : x = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18656
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq18656
    | exact resolve eq18656 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18656
  have eq18698 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq7173 y x
       grind)
    | (have r₁ := eq18678
       have r₂ := eq7173 y x
       grind)
    | exact resolve eq18678 eq7173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7173 eq18678
  have eq18737 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18645
       have i₂ := eq11898
       grind)
    | exact superpose eq11898 eq18645
    | exact resolve eq18645 eq11898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11898 eq18645
  have eq18740 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq18737
  have eq19545 : (τ (σ x)) = (k y (τ (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq261 (σ y) y
       have i₂ := eq18698
       grind)
    | exact superpose eq18698 eq261
    | exact resolve eq261 eq18698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq18698
  have eq19582 : (τ (σ x)) = (k y (τ (σ y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19545
       have r₂ := eq18740
       grind)
    | exact resolve eq19545 eq18740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18740 eq19545
  have eq19602 : (k y y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19582
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq19582
    | exact resolve eq19582 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19582
  have eq19609 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19602
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq19602
    | exact resolve eq19602 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19602
  have eq19860 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2543 y y
       have i₂ := eq19609
       grind)
    | exact superpose eq19609 eq2543
    | exact resolve eq2543 eq19609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2543 eq19609
  have eq19870 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19860
       have r₂ := eq18126
       grind)
    | exact resolve eq19860 eq18126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18126 eq19860
  have eq20544 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq19870
       grind)
    | exact superpose eq19870 eq16
    | exact resolve eq16 eq19870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq19870
  have eq20563 : x = (M.op x y) := by grind
  clear eq20544
  have eq20976 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17743
       have i₂ := eq20563
       grind)
    | exact superpose eq20563 eq17743
    | exact resolve eq17743 eq20563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17743
  have eq20977 : ∀ X0 : G, (M.op y X0) = (k X0 y) ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 y X0 x
       have i₂ := eq20563
       grind)
    | exact superpose eq20563 eq23
    | (have j0 := eq23 y X0 x
       grind)
    | exact resolve eq23 eq20563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq20988 : x = (M.op y y) := by grind
  clear eq20976
  have eq21546 : ∀ X0 : G, y = (M.op y (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq8 y X0
       have i₂ := eq20988
       grind)
    | exact superpose eq20988 eq8
    | exact resolve eq8 eq20988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27562 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq961 y
       have i₂ := eq20977 y
       grind)
    | exact superpose eq20977 eq961
    | (have j1 := eq20977 y
       grind)
    | exact resolve eq961 eq20977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961 eq20977
  have eq27607 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq7100 y
       grind)
    | (have r₁ := eq27562
       have r₂ := eq7100 y
       grind)
    | exact resolve eq27562 eq7100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7100 eq27562
  have eq27612 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq27607
       have i₂ := eq20988
       grind)
    | exact superpose eq20988 eq27607
    | exact resolve eq27607 eq20988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27607
  have eq31615 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq27612
       grind)
    | exact superpose eq27612 eq14
    | exact resolve eq14 eq27612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27612
  have eq31659 : (σ x) ≠ (σ x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq31615
       have i₂ := eq20563
       grind)
    | exact superpose eq20563 eq31615
    | exact resolve eq31615 eq20563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20563 eq31615
  have eq31660 : y = (M.op y x) := by grind
  clear eq31659
  have eq32571 : y = (M.op y y) := by
    first
    | (have i₁ := eq21546 y
       have i₂ := eq31660
       grind)
    | exact superpose eq31660 eq21546
    | exact resolve eq21546 eq31660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21546
  have eq32592 : x = y := by
    first
    | (have i₁ := eq32571
       have i₂ := eq20988
       grind)
    | exact superpose eq20988 eq32571
    | exact resolve eq32571 eq20988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20988 eq32571
  have eq33253 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq32592
       grind)
    | exact superpose eq32592 eq14
    | exact resolve eq14 eq32592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33261 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11899
       have i₂ := eq32592
       grind)
    | exact superpose eq32592 eq11899
    | exact resolve eq11899 eq32592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11899
  have eq33296 : x = (M.op x x) := by
    first
    | (have i₁ := eq31660
       have i₂ := eq32592
       grind)
    | exact superpose eq32592 eq31660
    | exact resolve eq31660 eq32592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31660 eq32592
  have eq33306 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq33261
  have eq33310 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq33253
       have i₂ := eq33296
       grind)
    | exact superpose eq33296 eq33253
    | exact resolve eq33253 eq33296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33253 eq33296
  have eq33311 : False := by grind
  exact eq33311

/-- `Equation52`: `x = x ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pxy_Equation52 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law52 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law52.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq8 (M.op X0 X0) X0
       have i₂ := eq8 X0 (M.op X0 X0)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq22 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq16 X0
       have i₂ := eq12 (M.op X0 X0) X1
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq26 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  clear eq19
  have eq42 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33
    | exact resolve eq33 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq31
    | exact resolve eq31 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq48 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq31
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq31 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq46
    | exact resolve eq46 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq24
    | exact resolve eq24 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq24 (τ X0) X1
       grind)
    | exact superpose eq24 eq18
    | (have j1 := eq24 (τ X0) X1
       grind)
    | exact resolve eq18 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq24
  have eq90 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X1
       have i₂ := eq12 X0 (τ X1)
       grind)
    | (have i₁ := eq42 X0
       have i₂ := eq12 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact superpose eq12 eq42
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq202 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (σ X1)
       have i₂ := eq26 X0 X1
       grind)
    | exact superpose eq26 eq16
    | (have j1 := eq26 X0 X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1
       have i₂ := eq26 X0 X1
       grind)
    | exact superpose eq26 eq53
    | (have j1 := eq26 X0 X1
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq53
  have eq246 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq225 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq225
    | (have j0 := eq225 X0 X1
       grind)
    | exact resolve eq225 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq255 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq22 X0 (σ X1)
       grind)
    | exact superpose eq22 eq31
    | (have j1 := eq22 X0 (σ X1)
       grind)
    | exact resolve eq31 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq31
  have eq564 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq28
    | exact resolve eq28 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq594 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq28 X1 X0
       grind)
    | exact superpose eq28 eq10
    | (have j1 := eq28 X1 X0
       grind)
    | exact resolve eq10 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq637 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq564 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq564
    | (have j0 := eq564 X0 X1
       grind)
    | exact resolve eq564 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq663 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq59
    | exact resolve eq59 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq706 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq663 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq663
    | (have j0 := eq663 X0 X1
       grind)
    | exact resolve eq663 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq760 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1
       have i₂ := eq637 X0 X1
       grind)
    | (have i₁ := eq16 X0
       have i₂ := eq637 (M.op X0 X0) X1
       grind)
    | exact superpose eq637 eq16
    | (have j1 := eq637 X0 X1
       grind)
    | exact resolve eq16 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq961 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (σ x)
       have i₂ := eq54 x x
       grind)
    | exact superpose eq54 eq16
    | (have j1 := eq54 X0 X0
       grind)
    | exact resolve eq16 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1440 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq202 x y
       grind)
    | exact superpose eq202 eq14
    | (have j1 := eq202 x y
       grind)
    | exact resolve eq14 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1454 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq202 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq3047 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq90 X1 (σ X0)
       grind)
    | exact superpose eq90 eq13
    | (have j1 := eq90 X1 (σ X0)
       grind)
    | exact resolve eq13 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3108 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3047 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3047
    | (have j0 := eq3047 X0 X1
       grind)
    | exact resolve eq3047 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3047
  have eq5856 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1454 (τ X0) (τ X1)
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq1454
    | (have j0 := eq1454 (τ X0) (τ X1)
       grind)
    | exact resolve eq1454 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq5896 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5856 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq5856
    | (have j0 := eq5856 X0 X1
       grind)
    | exact resolve eq5856 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5856
  have eq5901 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5896 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5896
    | (have j0 := eq5896 X0 X1
       grind)
    | exact resolve eq5896 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5896
  have eq5902 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5901 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5901
    | (have j0 := eq5901 X0 X1
       grind)
    | exact resolve eq5901 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5901
  have eq5903 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5902 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5902
    | (have j0 := eq5902 X0 X1
       grind)
    | exact resolve eq5902 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5902
  have eq10126 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq246 x y
       grind)
    | exact superpose eq246 eq14
    | (have j1 := eq246 x y
       grind)
    | exact resolve eq14 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq10159 : y = (k x y) := by
    first
    | (have j1 := eq706 x y
       grind)
    | (have r₁ := eq10126
       have r₂ := eq706 x y
       grind)
    | exact resolve eq10126 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706 eq10126
  have eq10383 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq637 x y
       have i₂ := eq10159
       grind)
    | exact superpose eq10159 eq637
    | (have j0 := eq637 x y
       grind)
    | exact resolve eq637 eq10159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10384 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq760 x y
       have i₂ := eq10159
       grind)
    | exact superpose eq10159 eq760
    | (have j0 := eq760 x y
       grind)
    | exact resolve eq760 eq10159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10385 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1454 x y
       have i₂ := eq10159
       grind)
    | exact superpose eq10159 eq1454
    | (have j0 := eq1454 x y
       grind)
    | exact resolve eq1454 eq10159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1454 eq10159
  have eq15690 : ∀ X0 : G, (k X0 (σ (τ X0))) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq594 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq15691 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq15690 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15690
    | (have j0 := eq15690 X0
       grind)
    | exact resolve eq15690 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15690
  have eq15855 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15691 (σ X0)
       have i₂ := eq90 X0 (σ X0)
       grind)
    | exact superpose eq90 eq15691
    | (have j0 := eq15691 (σ X0)
       have j1 := eq90 X0 (σ X0)
       grind)
    | (have r₁ := eq15691 (σ X0)
       have r₂ := eq90 X0 (σ X0)
       grind)
    | exact resolve eq15691 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq15691
  have eq15859 : ∀ X0 : G, (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq15855 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15855
  have eq15862 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15859 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq15859
    | (have j0 := eq15859 X0
       grind)
    | exact resolve eq15859 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15859
  have eq15871 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq15862 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq15862
    | (have j0 := eq15862 X0
       grind)
    | exact resolve eq15862 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15862
  have eq17857 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1440
       have i₂ := eq637 x y
       grind)
    | exact superpose eq637 eq1440
    | (have j1 := eq637 x y
       grind)
    | (have r₁ := eq1440
       have r₂ := eq637 x y
       grind)
    | exact resolve eq1440 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq17859 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1440
       have i₂ := eq760 x y
       grind)
    | exact superpose eq760 eq1440
    | (have j1 := eq760 (σ x) (σ y)
       grind)
    | (have r₁ := eq1440
       have r₂ := eq760 x y
       grind)
    | exact resolve eq1440 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760 eq1440
  have eq17863 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17859
  have eq17865 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq17857
  have eq17885 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq17865
       grind)
    | exact superpose eq17865 eq14
    | exact resolve eq14 eq17865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17865
  have eq18279 : (σ x) ≠ (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17885
       have i₂ := eq10383
       grind)
    | exact superpose eq10383 eq17885
    | exact resolve eq17885 eq10383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10383
  have eq18281 : (σ x) ≠ (σ y) ∨ x = (M.op y y) := by grind
  clear eq18279
  have eq18807 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq17863
       grind)
    | exact superpose eq17863 eq14
    | exact resolve eq14 eq17863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18819 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq48 (σ x) y
       have i₂ := eq17863
       grind)
    | exact superpose eq17863 eq48
    | (have j0 := eq48 (σ x) y
       grind)
    | exact resolve eq48 eq17863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq17863
  have eq18839 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18819
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq18819
    | exact resolve eq18819 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18819
  have eq18859 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq5903 x y
       grind)
    | (have r₁ := eq18839
       have r₂ := eq5903 x y
       grind)
    | exact resolve eq18839 eq5903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5903 eq18839
  have eq18899 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18807
       have i₂ := eq10384
       grind)
    | exact superpose eq10384 eq18807
    | exact resolve eq18807 eq10384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10384 eq18807
  have eq18902 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq18899
  have eq19722 : (τ (σ x)) = (k (τ (σ y)) y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq255 (σ y) y
       have i₂ := eq18859
       grind)
    | exact superpose eq18859 eq255
    | exact resolve eq255 eq18859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq18859
  have eq19759 : (τ (σ x)) = (k (τ (σ y)) y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19722
       have r₂ := eq18902
       grind)
    | exact resolve eq19722 eq18902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18902 eq19722
  have eq19779 : (k y y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19759
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq19759
    | exact resolve eq19759 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19759
  have eq19786 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19779
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq19779
    | exact resolve eq19779 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19779
  have eq20033 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3108 y y
       have i₂ := eq19786
       grind)
    | exact superpose eq19786 eq3108
    | exact resolve eq3108 eq19786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3108 eq19786
  have eq20043 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20033
       have r₂ := eq18281
       grind)
    | exact resolve eq20033 eq18281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18281 eq20033
  have eq20720 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq20043
       grind)
    | exact superpose eq20043 eq16
    | exact resolve eq16 eq20043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq20043
  have eq20739 : x = (M.op x y) := by grind
  clear eq20720
  have eq21192 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17885
       have i₂ := eq20739
       grind)
    | exact superpose eq20739 eq17885
    | exact resolve eq17885 eq20739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17885
  have eq21204 : x = (M.op y y) := by grind
  clear eq21192
  have eq21779 : x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq15871 y
       have i₂ := eq21204
       grind)
    | exact superpose eq21204 eq15871
    | exact resolve eq15871 eq21204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15871 eq21204
  have eq23522 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq961 y
       have i₂ := eq21779
       grind)
    | exact superpose eq21779 eq961
    | exact resolve eq961 eq21779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961 eq21779
  have eq23563 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq23522
  have eq23567 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq23563
       have r₂ := eq10385
       grind)
    | exact resolve eq23563 eq10385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10385 eq23563
  have eq24230 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq23567
       grind)
    | exact superpose eq23567 eq14
    | exact resolve eq14 eq23567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23567
  have eq24274 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq24230
       have i₂ := eq20739
       grind)
    | exact superpose eq20739 eq24230
    | exact resolve eq24230 eq20739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20739 eq24230
  have eq24275 : False := by grind
  exact eq24275

/-- `Equation53`: `x = x ◇ (y ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,m(X,X)) = m(Y,X) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxpxx_pyx_pxx_pxy_Equation53 :
    AutBox.GuardAut ((Lf 0) ⋆ ((Lf 0) ⋆ (Lf 0))) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law53 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ ((Lf 0) ⋆ (Lf 0))) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law53.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a (M.op a a) ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a (M.op a a)) (M.op b a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a (M.op a a) = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a (M.op a a)) (M.op b a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = X0 := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X1)) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 (M.op X1 (M.op X0 X1))
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq21 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq24 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X1
       have i₂ := eq12 X1 X0
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 (M.op X0 X0)))) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (M.op (σ X0) (σ X0))) = (M.op (σ X1) (σ X0)) := by
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
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq28
    | (have j0 := eq28 X0 X1
       grind)
    | exact resolve eq28 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq49 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X1 (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 (M.op X0 X1)) X0
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8
    | exact resolve eq8 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq54 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21
    | exact resolve eq21 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq32 (σ X0) (σ X1)
       grind)
    | exact superpose eq32 eq13
    | (have j1 := eq32 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq32 (τ X0) X1
       grind)
    | exact superpose eq32 eq16
    | (have j1 := eq32 (τ X0) X1
       grind)
    | exact resolve eq16 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0 X1
       have i₂ := eq32 X0 (σ X1)
       grind)
    | exact superpose eq32 eq21
    | (have j1 := eq32 X0 (σ X1)
       grind)
    | exact resolve eq21 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq32
  have eq113 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq31
    | exact resolve eq31 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (k X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq31 X0 (τ X1)
       grind)
    | exact superpose eq31 eq17
    | (have j1 := eq31 X0 (τ X1)
       grind)
    | exact resolve eq17 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq150 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq49
    | (have j1 := eq24 X1 X0
       grind)
    | exact resolve eq49 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq157 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X1 (M.op X1 X1)) ∨ (M.op X1 (M.op X0 (M.op X1 X0))) = (k X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 (M.op X1 X0))
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq12
    | (have j0 := eq12 X1 (M.op X0 (M.op X1 X0))
       grind)
    | exact resolve eq12 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X1 (M.op X1 X1)) ∨ (M.op X1 X1) = (k X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 (M.op X1 X0))
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq11
    | (have j0 := eq11 X1 (M.op X0 (M.op X1 X0))
       grind)
    | (have r₁ := eq11 X0 (M.op X0 (M.op X0 X0))
       have r₂ := eq49 X0 X0
       grind)
    | exact resolve eq11 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq161 : ∀ X0 X1 : G, (k X1 (M.op X0 (M.op X1 X0))) = X1 ∨ (M.op X0 (M.op X1 X0)) = (M.op X1 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq157 X0 X1
       have i₂ := eq8 X1 X0
       grind)
    | exact superpose eq8 eq157
    | (have j0 := eq157 X0 X1
       grind)
    | exact resolve eq157 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq193 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq150 (σ X0) (σ X1)
       grind)
    | exact superpose eq150 eq13
    | (have j1 := eq150 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq150 X0 (τ X1)
       grind)
    | exact superpose eq150 eq17
    | (have j1 := eq150 X0 (τ X1)
       grind)
    | exact resolve eq17 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq618 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq136 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq651 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq618 (σ X0)
       grind)
    | exact superpose eq618 eq13
    | exact resolve eq13 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq653 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq54 X0 X0
       have i₂ := eq618 (τ X0)
       grind)
    | exact superpose eq618 eq54
    | exact resolve eq54 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq660 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq653 X0
       have i₂ := eq618 X0
       grind)
    | exact superpose eq618 eq653
    | exact resolve eq653 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq662 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq651 X0
       have i₂ := eq618 X0
       grind)
    | exact superpose eq618 eq651
    | exact resolve eq651 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618 eq651
  have eq892 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq8 (σ X0) (σ X0)
       have i₂ := eq662 X0
       grind)
    | exact superpose eq662 eq8
    | exact resolve eq8 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1359 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq1414 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1359 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1359
    | (have j0 := eq1359 X0 X1
       grind)
    | exact resolve eq1359 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1359
  have eq1794 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (M.op (σ X1) (σ X1))) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 X0
       have i₂ := eq64 X1 X0
       grind)
    | exact superpose eq64 eq29
    | (have j0 := eq29 X1 X0
       have j1 := eq64 X1 X0
       grind)
    | exact resolve eq29 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq64
  have eq1813 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (M.op (σ X1) (σ X1))) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1794 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1794
  have eq1828 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ (M.op X1 X1))) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1813 X0 X1
       have i₂ := eq662 X1
       grind)
    | exact superpose eq662 eq1813
    | (have j0 := eq1813 X0 X1
       grind)
    | exact resolve eq1813 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1813
  have eq2426 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq134 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq134
    | exact resolve eq134 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq2583 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2426 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq2426
    | (have j0 := eq2426 X0 X1
       grind)
    | exact resolve eq2426 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2426
  have eq3532 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq197 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq197
    | exact resolve eq197 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq3607 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3532 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq3532
    | (have j0 := eq3532 X0 X1
       grind)
    | exact resolve eq3532 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3532
  have eq3748 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 X1)
       have i₂ := eq113 X0 X1
       grind)
    | exact superpose eq113 eq9
    | (have j1 := eq113 X0 X1
       grind)
    | exact resolve eq9 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq3884 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3748 X0 X1
       have i₂ := eq662 X0
       grind)
    | exact superpose eq662 eq3748
    | (have j0 := eq3748 X0 X1
       grind)
    | exact resolve eq3748 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3748
  have eq4010 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3884 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq3884
    | (have j0 := eq3884 X0 X1
       grind)
    | exact resolve eq3884 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3884
  have eq8511 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq4010 x y
       grind)
    | exact superpose eq4010 eq14
    | (have j1 := eq4010 x y
       grind)
    | exact resolve eq14 eq4010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4010
  have eq8592 : (k x y) = (M.op x x) := by
    first
    | (have j1 := eq2583 y x
       grind)
    | (have r₁ := eq8511
       have r₂ := eq2583 y x
       grind)
    | exact resolve eq8511 eq2583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2583 eq8511
  have eq8858 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq150 x y
       have i₂ := eq8592
       grind)
    | exact superpose eq8592 eq150
    | (have j0 := eq150 x y
       grind)
    | exact resolve eq150 eq8592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq8859 : (σ (M.op x y)) = (σ (M.op x x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1414 x y
       have i₂ := eq8592
       grind)
    | exact superpose eq8592 eq1414
    | (have j0 := eq1414 x y
       grind)
    | exact resolve eq1414 eq8592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1414
  have eq8861 : (σ (M.op x y)) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3607 y x
       have i₂ := eq8592
       grind)
    | exact superpose eq8592 eq3607
    | (have j0 := eq3607 y x
       grind)
    | exact resolve eq3607 eq8592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3607
  have eq9243 : x ≠ (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq8858
  have eq42079 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq193 x y
       grind)
    | exact superpose eq193 eq14
    | (have j1 := eq193 x y
       grind)
    | exact resolve eq14 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42217 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq193 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq42286 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq42079
       have i₂ := eq8592
       grind)
    | exact superpose eq8592 eq42079
    | exact resolve eq42079 eq8592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42079
  have eq42940 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq42217 (τ X0) (τ X1)
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq42217
    | (have j0 := eq42217 (τ X0) (τ X1)
       grind)
    | exact resolve eq42217 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq42974 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq42940 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq42940
    | (have j0 := eq42940 X0 X1
       grind)
    | exact resolve eq42940 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42940
  have eq42992 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq42974 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq42974
    | (have j0 := eq42974 X0 X1
       grind)
    | exact resolve eq42974 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42974
  have eq42997 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq42992 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq42992
    | (have j0 := eq42992 X0 X1
       grind)
    | exact resolve eq42992 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42992
  have eq43000 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq42997 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq42997
    | (have j0 := eq42997 X0 X1
       grind)
    | exact resolve eq42997 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42997
  have eq47833 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq42286
       have i₂ := eq8861
       grind)
    | exact superpose eq8861 eq42286
    | (have r₁ := eq42286
       have r₂ := eq8861
       grind)
    | exact resolve eq42286 eq8861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47834 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq42286
       have i₂ := eq8859
       grind)
    | exact superpose eq8859 eq42286
    | (have r₁ := eq42286
       have r₂ := eq8859
       grind)
    | exact resolve eq42286 eq8859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8859 eq42286
  have eq47835 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq47834
  have eq47836 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq47833
  have eq48424 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq47835
       grind)
    | exact superpose eq47835 eq14
    | exact resolve eq14 eq47835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47835
  have eq53010 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq47836
       grind)
    | exact superpose eq47836 eq14
    | exact resolve eq14 eq47836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53027 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq67 (σ x) y
       have i₂ := eq47836
       grind)
    | exact superpose eq47836 eq67
    | (have j0 := eq67 (σ x) y
       grind)
    | exact resolve eq67 eq47836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq47836
  have eq53114 : x = (k x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq53027
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq53027
    | exact resolve eq53027 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53027
  have eq53148 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq43000 (σ y) (σ x)
       grind)
    | (have r₁ := eq53114
       have r₂ := eq43000 x y
       grind)
    | exact resolve eq53114 eq43000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43000 eq53114
  have eq53775 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq53010
       have i₂ := eq8861
       grind)
    | exact superpose eq8861 eq53010
    | exact resolve eq53010 eq8861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8861 eq53010
  have eq53777 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x y) := by grind
  clear eq53775
  have eq58319 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8 (σ y) (σ x)
       have i₂ := eq53148
       grind)
    | exact superpose eq53148 eq8
    | exact resolve eq8 eq53148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53148
  have eq76751 : (σ y) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq161 (σ y) (σ x)
       have i₂ := eq58319
       grind)
    | exact superpose eq58319 eq161
    | exact resolve eq161 eq58319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58319
  have eq77245 : (σ y) = (M.op (σ x) (σ (M.op x x))) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq76751
       have i₂ := eq662 x
       grind)
    | exact superpose eq662 eq76751
    | exact resolve eq76751 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76751
  have eq77470 : (σ x) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ (M.op x x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77245
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq77245
    | exact resolve eq77245 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77245
  have eq77606 : (σ x) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ (M.op x x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77470
       have i₂ := eq8592
       grind)
    | exact superpose eq8592 eq77470
    | exact resolve eq77470 eq8592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8592 eq77470
  have eq77664 : (σ y) = (M.op (σ x) (σ (M.op x x))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq77606
       have r₂ := eq53777
       grind)
    | exact resolve eq77606 eq53777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53777 eq77606
  have eq78496 : (σ y) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ (M.op x x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq136 (σ x) (σ (M.op x x))
       have i₂ := eq77664
       grind)
    | exact superpose eq77664 eq136
    | exact resolve eq136 eq77664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78573 : (σ y) ≠ (σ (M.op x x)) ∨ (σ y) = (k (σ x) (σ (M.op x x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq78496
       have i₂ := eq662 x
       grind)
    | exact superpose eq662 eq78496
    | exact resolve eq78496 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78496
  have eq78624 : (σ y) = (σ (k x (M.op x x))) ∨ (σ y) ≠ (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq78573
       have i₂ := eq13 x (M.op x x)
       grind)
    | exact superpose eq13 eq78573
    | exact resolve eq78573 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78573
  have eq99583 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1828 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1828
    | exact resolve eq1828 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99641 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1828 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1828
    | exact resolve eq1828 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99690 : (σ y) = (σ (k x (M.op x x))) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1828 (M.op x x) x
       have i₂ := eq77664
       grind)
    | exact superpose eq77664 eq1828
    | exact resolve eq1828 eq77664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77664
  have eq100384 : (σ y) = (σ (k x (M.op x x))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq99690
       have r₂ := eq78624
       grind)
    | exact resolve eq99690 eq78624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78624 eq99690
  have eq100397 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq99641 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq99641
    | (have j0 := eq99641 X0 X1
       grind)
    | exact resolve eq99641 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99641
  have eq100420 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq99583 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq99583
    | (have j0 := eq99583 X0 X1
       grind)
    | exact resolve eq99583 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99583
  have eq100589 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ (τ (M.op X0 X0)))) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq100420 X0 X1
       have i₂ := eq660 X0
       grind)
    | exact superpose eq660 eq100420
    | (have j0 := eq100420 X0 X1
       grind)
    | exact resolve eq100420 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100420
  have eq100674 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ X1) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq100589 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq100589
    | (have j0 := eq100589 X0 X1
       grind)
    | exact resolve eq100589 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100589
  have eq103482 : (τ (σ y)) = (k x (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9 (k x (M.op x x))
       have i₂ := eq100384
       grind)
    | exact superpose eq100384 eq9
    | exact resolve eq9 eq100384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100384
  have eq103726 : y = (k x (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq103482
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq103482
    | exact resolve eq103482 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103482
  have eq107148 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq100674 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq100674
    | exact resolve eq100674 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100674
  have eq125004 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq158 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq152008 : ∀ X0 X1 : G, (σ (k X1 (M.op X1 X1))) = X0 ∨ (σ (M.op X1 X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1828 (M.op X1 X1) X1
       have i₂ := eq100397 X0 X1
       grind)
    | (have i₁ := eq1828 X0 X1
       have i₂ := eq100397 (M.op (σ X1) (σ X0)) X1
       grind)
    | exact superpose eq100397 eq1828
    | (have j1 := eq100397 X0 X1
       grind)
    | exact resolve eq1828 eq100397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828
  have eq152021 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) ≠ X0 ∨ (k (σ X1) (σ (M.op X1 X1))) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq136 (σ X1) (σ (M.op X1 X1))
       have i₂ := eq100397 X0 X1
       grind)
    | (have i₁ := eq136 X0 X1
       have i₂ := eq100397 (M.op X0 X1) X1
       grind)
    | exact superpose eq100397 eq136
    | (have j0 := eq136 (σ X1) X0
       have j1 := eq100397 X0 X1
       grind)
    | (have r₁ := eq136 (σ X1) (σ (M.op X1 X1))
       have r₂ := eq100397 (M.op (σ X1) (σ X1)) X1
       grind)
    | exact resolve eq136 eq100397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq100397
  have eq152024 : ∀ X0 X1 : G, (σ (M.op X1 X1)) ≠ X0 ∨ (k (σ X1) (σ (M.op X1 X1))) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq152021 X0 X1
       have i₂ := eq662 X1
       grind)
    | exact superpose eq662 eq152021
    | (have j0 := eq152021 X0 X1
       grind)
    | (have r₁ := eq152021 (σ (M.op X0 X0)) X0
       have r₂ := eq662 X0
       grind)
    | exact resolve eq152021 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152021
  have eq152038 : ∀ X0 X1 : G, (σ (k X1 (M.op X1 X1))) = X0 ∨ (σ (M.op X1 X1)) ≠ X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq152024 X0 X1
       have i₂ := eq13 X1 (M.op X1 X1)
       grind)
    | exact superpose eq13 eq152024
    | (have j0 := eq152024 X0 X1
       grind)
    | exact resolve eq152024 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152024
  have eq152044 : ∀ X0 X1 : G, (σ (k X1 (M.op X1 X1))) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq152038 X0 X1
       have j1 := eq152008 X0 X1
       grind)
    | (have r₁ := eq152038 (σ (k X1 (M.op X1 X1))) X1
       have r₂ := eq152008 (σ (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq152038 X0 X1
       have r₂ := eq152008 X0 X1
       grind)
    | (have r₁ := eq152038 (σ (M.op X1 X1)) X1
       have r₂ := eq152008 (σ (M.op X1 X1)) X1
       grind)
    | exact resolve eq152038 eq152008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152008 eq152038
  have eq152160 : ∀ X0 X1 : G, (k X1 (σ (M.op (τ X1) (τ X1)))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op (τ X1) (τ X1))
       have i₂ := eq152044 X0 (τ X1)
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq152044 (σ (k (τ X0) X1)) X1
       grind)
    | exact superpose eq152044 eq16
    | (have j1 := eq152044 X0 (τ X1)
       grind)
    | exact resolve eq16 eq152044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq152163 : ∀ X0 X1 : G, (τ X0) = (k X1 (M.op X1 X1)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 (M.op X1 X1))
       have i₂ := eq152044 X0 X1
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq152044 (σ X0) X1
       grind)
    | exact superpose eq152044 eq9
    | (have j1 := eq152044 X0 X1
       grind)
    | exact resolve eq9 eq152044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152044
  have eq152231 : ∀ X0 X1 : G, (k X1 (σ (τ (M.op X1 X1)))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq152160 X0 X1
       have i₂ := eq660 X1
       grind)
    | exact superpose eq660 eq152160
    | (have j0 := eq152160 X0 X1
       grind)
    | exact resolve eq152160 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660 eq152160
  have eq152238 : ∀ X0 X1 : G, (k X1 (M.op X1 X1)) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq152231 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq152231
    | (have j0 := eq152231 X0 X1
       grind)
    | exact resolve eq152231 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152231
  have eq152242 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq152238 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq152238
    | (have j0 := eq152238 X0 X1
       grind)
    | exact resolve eq152238 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152238
  have eq152539 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ x = (M.op x y) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq103726
       have i₂ := eq152242 X0 x
       grind)
    | (have i₁ := eq103726
       have i₂ := eq152242 (k x (M.op x x)) x
       grind)
    | exact superpose eq152242 eq103726
    | (have j1 := eq152242 X0 x
       grind)
    | exact resolve eq103726 eq152242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103726 eq152242
  have eq152748 : (M.op x x) = (M.op x (M.op x (M.op x x))) ∨ x = (M.op x y) ∨ y = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq125004 x
       have i₂ := eq152539 (M.op x (M.op x x))
       grind)
    | exact superpose eq152539 eq125004
    | (have j1 := eq152539 (M.op x (M.op x x))
       grind)
    | exact resolve eq125004 eq152539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125004 eq152539
  have eq152768 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq152748
       have i₂ := eq8 x x
       grind)
    | exact superpose eq8 eq152748
    | exact resolve eq152748 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152748
  have eq152771 : y = (M.op x (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq152768
       have r₂ := eq9243
       grind)
    | exact resolve eq152768 eq9243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9243 eq152768
  have eq152819 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8 x x
       have i₂ := eq152771
       grind)
    | exact superpose eq152771 eq8
    | exact resolve eq8 eq152771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152771
  have eq152860 : x = (M.op x y) := by grind
  clear eq152819
  have eq152919 : (σ x) ≠ (σ x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq48424
       have i₂ := eq152860
       grind)
    | exact superpose eq152860 eq48424
    | exact resolve eq48424 eq152860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48424
  have eq152946 : x = (k x (M.op y x)) ∨ (M.op x (M.op x x)) = (M.op y x) := by
    first
    | (have i₁ := eq161 y x
       have i₂ := eq152860
       grind)
    | exact superpose eq152860 eq161
    | exact resolve eq161 eq152860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq152971 : y = (M.op y x) := by grind
  clear eq152919
  have eq154781 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op y x))) ∨ (M.op x (M.op x x)) = (M.op y x) := by
    first
    | (have i₁ := eq42217 x (M.op y x)
       have i₂ := eq152946
       grind)
    | exact superpose eq152946 eq42217
    | (have j0 := eq42217 x (M.op y x)
       grind)
    | exact resolve eq42217 eq152946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42217 eq152946
  have eq154799 : (σ x) = (M.op (σ x) (σ (M.op y x))) ∨ (M.op x (M.op x x)) = (M.op y x) := by grind
  clear eq154781
  have eq154808 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x (M.op x x)) = (M.op y x) := by
    first
    | (have i₁ := eq154799
       have i₂ := eq152971
       grind)
    | exact superpose eq152971 eq154799
    | exact resolve eq154799 eq152971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154799
  have eq154814 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq154808
       have i₂ := eq152971
       grind)
    | exact superpose eq152971 eq154808
    | exact resolve eq154808 eq152971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152971 eq154808
  have eq154918 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq154814
       grind)
    | exact superpose eq154814 eq14
    | exact resolve eq14 eq154814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154814
  have eq154972 : (σ x) ≠ (σ x) ∨ y = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq154918
       have i₂ := eq152860
       grind)
    | exact superpose eq152860 eq154918
    | exact resolve eq154918 eq152860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154918
  have eq154973 : y = (M.op x (M.op x x)) := by grind
  clear eq154972
  have eq155019 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq107148 X0 x
       have i₂ := eq154973
       grind)
    | exact superpose eq154973 eq107148
    | (have j0 := eq107148 X0 x
       grind)
    | exact resolve eq107148 eq154973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107148
  have eq155215 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op x (τ X0))) ∨ (τ X0) = y := by
    intro X0
    first
    | (have i₁ := eq17 X0 x
       have i₂ := eq155019 (τ X0)
       grind)
    | exact superpose eq155019 eq17
    | (have j1 := eq155019 (τ X0)
       grind)
    | exact resolve eq17 eq155019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq156431 : ∀ X0 : G, (σ (M.op x X0)) = (k (σ x) (σ X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq155215 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq155215
    | exact resolve eq155215 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155215
  have eq156475 : ∀ X0 : G, (σ (k x X0)) = (σ (M.op x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq156431 X0
       have i₂ := eq13 x X0
       grind)
    | exact superpose eq13 eq156431
    | (have j0 := eq156431 X0
       grind)
    | exact resolve eq156431 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156431
  have eq162033 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X1)) = (k X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq152163 (σ X1) X0
       grind)
    | exact superpose eq152163 eq13
    | (have j1 := eq152163 (σ X1) X0
       grind)
    | exact resolve eq13 eq152163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152163
  have eq162070 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq162033 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq162033
    | (have j0 := eq162033 X0 X1
       grind)
    | exact resolve eq162033 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162033
  have eq164737 : ∀ X0 : G, (M.op x (M.op x x)) = X0 ∨ y = (M.op x x) ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq155019 (M.op x x)
       have i₂ := eq162070 x X0
       grind)
    | (have i₁ := eq155019 X0
       have i₂ := eq162070 X0 (k x X0)
       grind)
    | exact superpose eq162070 eq155019
    | (have j0 := eq155019 (M.op x x)
       have j1 := eq162070 x X0
       grind)
    | exact resolve eq155019 eq162070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155019 eq162070
  have eq164783 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ y = (M.op x x) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq164737 X0
       have i₂ := eq154973
       grind)
    | exact superpose eq154973 eq164737
    | (have j0 := eq164737 X0
       grind)
    | exact resolve eq164737 eq154973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164737
  have eq441726 : (σ x) = (M.op (σ x) (σ (k x (M.op x x)))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq892 x
       have i₂ := eq164783 (M.op x x)
       grind)
    | exact superpose eq164783 eq892
    | (have j1 := eq164783 (M.op x x)
       grind)
    | exact resolve eq892 eq164783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892 eq164783
  have eq441736 : (σ x) = (M.op (σ x) (σ (k x (M.op x x)))) ∨ y = (M.op x x) := by grind
  clear eq441726
  have eq444208 : (σ x) = (M.op (σ x) (σ (M.op x (M.op x x)))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq441736
       have i₂ := eq156475 (M.op x x)
       grind)
    | exact superpose eq156475 eq441736
    | (have j1 := eq156475 (M.op x x)
       grind)
    | exact resolve eq441736 eq156475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156475 eq441736
  have eq444223 : (σ x) = (M.op (σ x) (σ (M.op x (M.op x x)))) ∨ y = (M.op x x) := by grind
  clear eq444208
  have eq444231 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq444223
       have i₂ := eq154973
       grind)
    | exact superpose eq154973 eq444223
    | exact resolve eq444223 eq154973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444223
  have eq445241 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq444231
       grind)
    | exact superpose eq444231 eq14
    | exact resolve eq14 eq444231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444231
  have eq445323 : (σ x) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq445241
       have i₂ := eq152860
       grind)
    | exact superpose eq152860 eq445241
    | exact resolve eq445241 eq152860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445241
  have eq445324 : y = (M.op x x) := by grind
  clear eq445323
  have eq446388 : y = (M.op x y) := by
    first
    | (have i₁ := eq154973
       have i₂ := eq445324
       grind)
    | exact superpose eq445324 eq154973
    | exact resolve eq154973 eq445324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154973 eq445324
  have eq446782 : x = y := by
    first
    | (have i₁ := eq446388
       have i₂ := eq152860
       grind)
    | exact superpose eq152860 eq446388
    | exact resolve eq446388 eq152860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152860 eq446388
  have eq449761 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq446782
       grind)
    | exact superpose eq446782 eq14
    | exact resolve eq14 eq446782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446782
  have eq449962 : False := by grind
  exact eq449962

/-- `Equation543`: `x = y ◇ (z ◇ (x ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_pyx_pxy_Equation543 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law543 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law543.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X0 (M.op X1 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9
    | exact resolve eq9 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 (M.op X0 (M.op X1 X2))) (M.op X3 X0))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X1 (M.op X2 (M.op X0 (M.op X1 X2)))
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 (M.op X2 X1)) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 X1 (M.op X0 (M.op X2 X1))
       have i₂ := eq8 X0 X2 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq13
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20
    | exact resolve eq20 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = X1 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X0 X0
       have i₂ := eq12 X0 X2
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X2
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X0 X1))) ∨ (k (M.op X0 X1) X2) = (M.op (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X0 X1) X0 X1
       have i₂ := eq12 (M.op X0 X1) X2
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 (M.op X0 X1) X2
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X2
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X1
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) X1
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 (M.op X2 X1))) (M.op (M.op X3 X0) X3)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 X3 (M.op X1 (M.op X0 (M.op X2 X1))) X2
       have i₂ := eq8 X0 X2 X1
       grind)
    | exact superpose eq8 eq22
    | exact resolve eq22 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X0 X2)) X1) (M.op (M.op X3 X0) X3)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 X3 (M.op (M.op X1 (M.op X0 X2)) X1) X2
       have i₂ := eq22 X1 X2 X0
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) = X0 ∨ (k (M.op X0 X1) X2) = (M.op (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (M.op X0 X1) X1 X0
       have i₂ := eq12 (M.op X0 X1) X2
       grind)
    | exact superpose eq12 eq22
    | (have j1 := eq12 (M.op X0 X1) X2
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X1 (M.op X0 X2)) X1
       have i₂ := eq22 X1 X2 X0
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X2) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (M.op X1 X2) (M.op X0 X2)) X1 X2
       have i₂ := eq22 (M.op X1 X2) X2 X0
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op (M.op X2 (M.op X0 X1)) X2) (M.op X3 X0))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X1 (M.op (M.op X2 (M.op X0 X1)) X2)
       have i₂ := eq22 X2 X1 X0
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = X0 ∨ (k (M.op X0 X1) X2) = (M.op (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X0 X1 X2
       have i₂ := eq67 X0 X0 X1
       grind)
    | exact superpose eq67 eq65
    | (have j0 := eq65 X0 X1 X2
       grind)
    | exact resolve eq65 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq102 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq104 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X2 X3))) = (M.op (M.op X1 X0) (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq66 X2 X1 (M.op X3 (M.op X0 (M.op X2 X3)))
       have i₂ := eq8 X0 X2 X3
       grind)
    | exact superpose eq8 eq66
    | exact resolve eq66 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X2 (M.op X0 (M.op X1 X2))) X3)) X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq66 (M.op X2 (M.op X0 (M.op X1 X2))) X1 X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq66
    | exact resolve eq66 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op (M.op X2 (M.op X0 X1)) X2) X3)) X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq66 (M.op (M.op X2 (M.op X0 X1)) X2) X1 X3
       have i₂ := eq22 X2 X1 X0
       grind)
    | exact superpose eq22 eq66
    | exact resolve eq66 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 X2) (M.op (M.op X3 X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 X3 (M.op X1 X2) (M.op X1 (M.op X2 X0))
       have i₂ := eq66 X2 X1 X0
       grind)
    | exact superpose eq66 eq22
    | exact resolve eq22 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 (M.op X3 (M.op X2 (M.op X1 (M.op X1 X2)))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 (M.op X2 (M.op X1 (M.op X1 X2))) X0 X1 X3
       have i₂ := eq21 X1 X1 X2 X0
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 x X0 X1 X1
       have i₂ := eq66 x X1 (M.op X0 X1)
       grind)
    | exact superpose eq66 eq21
    | exact resolve eq21 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X3 (M.op X0 (M.op X2 (M.op X3 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X3 X1 X2 (M.op X3 (M.op X0 (M.op X2 (M.op X3 (M.op X1 X2)))))
       have i₂ := eq22 X3 (M.op X2 (M.op X3 (M.op X1 X2))) X0
       grind)
    | exact superpose eq22 eq21
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X1 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X2 (M.op X1 (M.op X1 X2))) X0 X1
       have i₂ := eq21 X1 X1 X2 X0
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X1 X2 X3 : G, (M.op X3 (M.op X2 (M.op X1 (M.op X1 X2)))) = X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq130 x X1 X2 X3
       have i₂ := eq137 x (M.op X3 (M.op X2 (M.op X1 (M.op X1 X2))))
       grind)
    | exact superpose eq137 eq130
    | exact resolve eq130 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq155 : ∀ X2 X3 : G, (M.op X3 (M.op X2 X2)) = X3 := by
    intro X2 X3
    first
    | (have i₁ := eq153 x X2 X3
       have i₂ := eq137 x X2
       grind)
    | exact superpose eq137 eq153
    | exact resolve eq153 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq157 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq155 X0 X1
       have i₂ := eq12 X0 X2
       grind)
    | exact superpose eq12 eq155
    | (have j1 := eq12 X0 X2
       grind)
    | exact resolve eq155 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X1) X2)) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 (M.op X1 X1) X0 X2
       have i₂ := eq155 X1 X0
       grind)
    | exact superpose eq155 eq66
    | exact resolve eq66 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 X0 X1 (M.op X2 X2)
       have i₂ := eq155 X2 X0
       grind)
    | exact superpose eq155 eq66
    | exact resolve eq66 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0) X1
       have i₂ := eq155 X0 (M.op X0 X0)
       grind)
    | exact superpose eq155 eq11
    | (have j0 := eq11 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq11 (M.op x x) X1
       have r₂ := eq155 x (M.op x x)
       grind)
    | exact resolve eq11 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq170 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq175 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq174 X0 X1
       have i₂ := eq155 X0 X1
       grind)
    | (have i₁ := eq174 X0 X1
       have i₂ := eq155 x (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq155 eq174
    | exact resolve eq174 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq177 : ∀ X1 X2 : G, (M.op X1 X1) = (M.op X2 X2) := by
    intro X1 X2
    first
    | (have i₁ := eq167 x X1 X2
       have i₂ := eq67 X1 X1 x
       grind)
    | exact superpose eq67 eq167
    | exact resolve eq167 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq180 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 (M.op X2 X1))) (M.op (M.op X1 (M.op X0 (M.op X2 X1))) X0)) = X2 ∨ (k (M.op X1 (M.op X0 (M.op X2 X1))) X3) = (M.op (M.op X1 (M.op X0 (M.op X2 X1))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq40 (M.op X1 (M.op X0 (M.op X2 X1))) X2 X3
       have i₂ := eq8 X0 X2 X1
       grind)
    | exact superpose eq8 eq40
    | (have j0 := eq40 (M.op X1 (M.op X0 (M.op X2 X1))) X1 X3
       grind)
    | exact resolve eq40 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq228 : ∀ X0 X1 X2 X3 : G, (k (M.op X1 (M.op X0 (M.op X2 X1))) X3) = (M.op (M.op X1 (M.op X0 (M.op X2 X1))) X3) ∨ X0 = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq180 X0 X1 X2 X3
       have i₂ := eq137 (M.op X1 (M.op X0 (M.op X2 X1))) X0
       grind)
    | exact superpose eq137 eq180
    | (have j0 := eq180 X0 X1 X2 X3
       grind)
    | exact resolve eq180 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq231 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq137 X1 (M.op (M.op X2 (M.op X0 X1)) X2)
       have i₂ := eq22 X2 X1 X0
       grind)
    | exact superpose eq22 eq137
    | exact resolve eq137 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq235 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq137 (M.op X1 (M.op X2 X0)) (M.op X1 X2)
       have i₂ := eq66 X2 X1 X0
       grind)
    | exact superpose eq66 eq137
    | exact resolve eq137 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 (M.op X1 X0) X1 X2
       have i₂ := eq137 X1 X0
       grind)
    | exact superpose eq137 eq66
    | exact resolve eq66 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 X0) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 X2 X1 (M.op X2 X0)
       have i₂ := eq137 X2 X0
       grind)
    | exact superpose eq137 eq66
    | exact resolve eq66 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 X2))) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X0 X1 X2 (M.op X2 (M.op X0 (M.op X1 X2)))
       have i₂ := eq137 (M.op X2 (M.op X0 (M.op X1 X2))) X0
       grind)
    | exact superpose eq137 eq21
    | exact resolve eq21 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq273 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq43 x y
       grind)
    | exact superpose eq43 eq14
    | (have j1 := eq43 x x
       grind)
    | exact resolve eq14 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (σ X1) (M.op X2 (σ (k X0 X1))))) = X2 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (σ X0) (σ X1)
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq8
    | (have j1 := eq43 X0 X1
       grind)
    | exact resolve eq8 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq309 : ∀ X0 X1 X2 : G, (k X0 X1) = X1 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq175 X0 X1
       have i₂ := eq12 X0 X2
       grind)
    | exact superpose eq12 eq175
    | (have j1 := eq12 X0 X2
       grind)
    | exact resolve eq175 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq316 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X1 X1)
       have i₂ := eq175 X1 (τ X0)
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (M.op X1 X1) X0
       have i₂ := eq175 X1 (σ X0)
       grind)
    | exact superpose eq175 eq20
    | exact resolve eq20 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 X1 : G, (k (τ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq317 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq317
    | exact resolve eq317 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq324 : ∀ X0 X1 : G, (k (σ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq316 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq316
    | exact resolve eq316 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq482 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X0) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X2 X1 X1
       have i₂ := eq177 X1 X0
       grind)
    | (have i₁ := eq67 X2 X1 X1
       have i₂ := eq177 X0 X1
       grind)
    | exact superpose eq177 eq67
    | exact resolve eq67 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq485 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq67 X3 (M.op X0 X2) (M.op X1 X2)
       have i₂ := eq67 X1 X0 X2
       grind)
    | exact superpose eq67 eq67
    | exact resolve eq67 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq498 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op X3 X0))) = (M.op (M.op X1 (M.op X2 X3)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq67 (M.op X2 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq66 X3 X2 X0
       grind)
    | exact superpose eq66 eq67
    | exact resolve eq67 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq592 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) = (M.op (M.op X1 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) ∨ (M.op (M.op X0 X1) X3) = (k (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq140 X2 X0 (M.op X1 (M.op X0 X1))
       have i₂ := eq41 X0 X1 X3
       grind)
    | exact superpose eq41 eq140
    | (have j1 := eq41 X0 X1 X3
       grind)
    | exact resolve eq140 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq718 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 X2) ∨ (M.op (M.op X0 X1) X3) = (k (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq592 X0 X1 X2 X3
       have i₂ := eq67 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq67 eq592
    | (have j0 := eq592 X0 X1 X2 X3
       grind)
    | exact resolve eq592 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq777 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (σ (M.op X1 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (σ (M.op X1 X1))
       have i₂ := eq324 (τ X0) X1
       grind)
    | exact superpose eq324 eq16
    | exact resolve eq16 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq786 : ∀ X0 X1 : G, (k (σ (σ (M.op X1 X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq777 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq777
    | exact resolve eq777 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq803 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq102 X1 X1
       have i₂ := eq177 X1 x
       grind)
    | (have i₁ := eq102 x x
       have i₂ := eq177 X1 x
       grind)
    | exact superpose eq177 eq102
    | (have j0 := eq102 X0 X0
       grind)
    | (have r₁ := eq102 x x
       have r₂ := eq177 x x
       grind)
    | (have r₁ := eq102 X1 X1
       have r₂ := eq177 X1 X1
       grind)
    | exact resolve eq102 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq809 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq102 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq812 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq803 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq838 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq809 (σ X0)
       grind)
    | exact superpose eq809 eq13
    | exact resolve eq13 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq847 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq838 X0
       have i₂ := eq809 X0
       grind)
    | exact superpose eq809 eq838
    | exact resolve eq838 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq964 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (σ X1)
       have i₂ := eq812 X0 (σ X1)
       grind)
    | exact superpose eq812 eq28
    | exact resolve eq28 eq812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq965 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq324 (σ (M.op X1 X1)) X1
       have i₂ := eq812 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq812 eq324
    | exact resolve eq324 eq812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq967 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X1)
       have i₂ := eq812 X0 (τ X1)
       grind)
    | exact superpose eq812 eq15
    | exact resolve eq15 eq812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq968 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq323 (τ (M.op X1 X1)) X1
       have i₂ := eq812 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq812 eq323
    | exact resolve eq323 eq812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323 eq812
  have eq973 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq967 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq967
    | exact resolve eq967 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967
  have eq975 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq964 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq964
    | exact resolve eq964 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964
  have eq1215 : ∀ X0 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq965 x X2
       have i₂ := eq965 x X0
       grind)
    | exact superpose eq965 eq965
    | exact resolve eq965 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1225 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq965 X1 x
       have i₂ := eq965 x X0
       grind)
    | exact superpose eq965 eq965
    | exact resolve eq965 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1262 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq155 x X1
       have i₂ := eq965 x X0
       grind)
    | exact superpose eq965 eq155
    | exact resolve eq155 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965
  have eq1392 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq968 X1 x
       have i₂ := eq968 x X0
       grind)
    | exact superpose eq968 eq968
    | exact resolve eq968 eq968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1424 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq155 x X1
       have i₂ := eq968 x X0
       grind)
    | exact superpose eq968 eq155
    | exact resolve eq155 eq968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2157 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1262 X0 X1
       have i₂ := eq12 X0 X2
       grind)
    | exact superpose eq12 eq1262
    | (have j1 := eq12 X0 X2
       grind)
    | exact resolve eq1262 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2165 : ∀ X0 X1 : G, (M.op X1 (σ (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1262 (σ (M.op X0 X0)) X1
       have i₂ := eq1262 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq1262 eq1262
    | exact resolve eq1262 eq1262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2266 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X3) X4) = (M.op (M.op (M.op X1 X0) X1) (M.op (M.op X5 (M.op (M.op X2 (M.op X3 X0)) X2)) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq62 (M.op (M.op X2 (M.op X3 X0)) X2) X1 (M.op (M.op X4 X3) X4) X5
       have i₂ := eq62 X3 X2 X0 X4
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2349 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 (M.op X2 X0)) X1) X3) = (M.op X0 (M.op X3 (M.op (M.op X4 X2) X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq67 X3 (M.op (M.op X1 (M.op X2 X0)) X1) (M.op (M.op X4 X2) X4)
       have i₂ := eq62 X2 X1 X0 X4
       grind)
    | exact superpose eq62 eq67
    | exact resolve eq67 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2364 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X0 X2) X3) = (M.op X0 (M.op X3 (M.op (M.op X4 X2) X4))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq2349 X0 x X2 X3 X4
       have i₂ := eq231 X2 X0 x
       grind)
    | exact superpose eq231 eq2349
    | exact resolve eq2349 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2349
  have eq2432 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) X4) = (M.op (M.op X1 X0) (M.op X1 (M.op (M.op X2 (M.op X3 X0)) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2266 X0 X1 X2 X3 X4 x
       have i₂ := eq116 (M.op (M.op X2 (M.op X3 X0)) X2) (M.op X1 X0) X1 x
       grind)
    | exact superpose eq116 eq2266
    | exact resolve eq2266 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq2266
  have eq2509 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X4 X3) X4) = (M.op (M.op (M.op X1 X0) (M.op X3 X0)) X1) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq2432 X0 X1 x X3 X4
       have i₂ := eq2364 (M.op X1 X0) (M.op X3 X0) X1 x
       grind)
    | exact superpose eq2364 eq2432
    | exact resolve eq2432 eq2364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2364 eq2432
  have eq2541 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X4 X3) X4) = (M.op (M.op X1 X0) (M.op X3 (M.op X0 X1))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq2509 X0 X1 X3 X4
       have i₂ := eq498 X1 (M.op X1 X0) X3 X0
       grind)
    | exact superpose eq498 eq2509
    | exact resolve eq2509 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2509
  have eq2553 : ∀ X1 X3 X4 : G, (M.op (M.op X4 X3) X4) = (M.op (M.op X1 X1) X3) := by
    intro X1 X3 X4
    first
    | (have i₁ := eq2541 x X1 X3 X4
       have i₂ := eq485 X1 x X1 X3
       grind)
    | exact superpose eq485 eq2541
    | exact resolve eq2541 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2541
  have eq2569 : ∀ X0 X1 : G, (M.op X1 (τ (τ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1424 (τ (M.op X0 X0)) X1
       have i₂ := eq1424 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq1424 eq1424
    | exact resolve eq1424 eq1424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1424
  have eq2703 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X0 (M.op X2 (M.op X3 (M.op X0 X2)))) (M.op X4 (M.op X1 X3)))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq68 (M.op X1 X3) X1 (M.op X2 (M.op X3 (M.op X0 X2))) X4
       have i₂ := eq61 X3 X2 X0 X1
       grind)
    | exact superpose eq61 eq68
    | exact resolve eq68 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2858 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 (M.op X0 X2)) (M.op X4 (M.op X1 X3)))))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2703 X0 X1 X2 X3 X4
       have i₂ := eq498 (M.op X4 (M.op X1 X3)) X0 X2 (M.op X3 (M.op X0 X2))
       grind)
    | exact superpose eq498 eq2703
    | exact resolve eq2703 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2703
  have eq2937 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X3 (M.op X0 (M.op X2 (M.op X4 (M.op X1 X3)))))))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2858 X0 X1 X2 X3 X4
       have i₂ := eq498 (M.op X4 (M.op X1 X3)) X3 X0 X2
       grind)
    | exact superpose eq498 eq2858
    | exact resolve eq2858 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2858
  have eq3081 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X0)) X3) = (M.op X4 (M.op X3 (M.op (M.op X1 X2) (M.op X4 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq138 X3 (M.op X1 (M.op X2 X0)) (M.op X1 X2) X4
       have i₂ := eq66 X2 X1 X0
       grind)
    | exact superpose eq66 eq138
    | exact resolve eq138 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq3107 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op X4 (M.op X2 (M.op X0 X4))) (M.op X3 (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq138 X3 (M.op X1 X2) X1 (M.op X4 (M.op X2 (M.op X0 X4)))
       have i₂ := eq61 X2 X4 X0 X1
       grind)
    | exact superpose eq61 eq138
    | exact resolve eq138 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq3108 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op (M.op X4 (M.op X2 X0)) X4) (M.op X3 (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq138 X3 (M.op X1 X2) X1 (M.op (M.op X4 (M.op X2 X0)) X4)
       have i₂ := eq62 X2 X4 X0 X1
       grind)
    | exact superpose eq62 eq138
    | exact resolve eq138 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq3132 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X1)) = (M.op X2 (M.op X0 (M.op X3 (M.op X2 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq138 (M.op X0 (M.op X3 (M.op X2 X1))) X2 X1 X3
       have i₂ := eq67 X1 X0 (M.op X3 (M.op X2 X1))
       grind)
    | exact superpose eq67 eq138
    | exact resolve eq138 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3174 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X1)) = (M.op X1 (M.op X3 (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq137 X2 (M.op X1 (M.op X3 (M.op X2 (M.op X0 X3))))
       have i₂ := eq138 X1 X0 X3 X2
       grind)
    | exact superpose eq138 eq137
    | exact resolve eq137 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3181 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X1 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3174 X0 X1 X2 x
       have i₂ := eq254 X2 X0 x
       grind)
    | exact superpose eq254 eq3174
    | exact resolve eq3174 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3174
  have eq3230 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op X0 X2) (M.op X3 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3108 X0 X1 X2 X3 x
       have i₂ := eq231 X2 X0 x
       grind)
    | exact superpose eq231 eq3108
    | exact resolve eq3108 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231 eq3108
  have eq3231 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) X3) = (M.op X4 (M.op X2 (M.op (M.op X0 X4) (M.op X3 (M.op X1 X0))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3107 X0 X1 X2 X3 X4
       have i₂ := eq498 (M.op X3 (M.op X1 X0)) X4 X2 (M.op X0 X4)
       grind)
    | exact superpose eq498 eq3107
    | exact resolve eq3107 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3107
  have eq3253 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3081 X0 X1 X2 X3 x
       have i₂ := eq3132 X3 X0 x (M.op X1 X2)
       grind)
    | exact superpose eq3132 eq3081
    | exact resolve eq3081 eq3132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3081
  have eq3306 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X1 X2) X3) = (M.op X4 (M.op X2 (M.op (M.op X1 X4) X3))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq3231 x X1 X2 X3 X4
       have i₂ := eq3230 x X1 X4 X3
       grind)
    | exact superpose eq3230 eq3231
    | exact resolve eq3231 eq3230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3230 eq3231
  have eq3318 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op X3 X0)) = (M.op X1 (M.op X2 (M.op X0 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3253 X0 X1 X2 X3
       have i₂ := eq498 X3 X1 X2 X0
       grind)
    | exact superpose eq498 eq3253
    | exact resolve eq3253 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3253
  have eq3437 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq975 X1 (σ (σ (M.op X0 X0)))
       have i₂ := eq786 (σ (σ (M.op X0 X0))) X0
       grind)
    | exact superpose eq786 eq975
    | exact resolve eq975 eq786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975
  have eq3438 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq973 X1 (σ (σ (M.op X0 X0)))
       have i₂ := eq786 (σ (σ (M.op X0 X0))) X0
       grind)
    | exact superpose eq786 eq973
    | exact resolve eq973 eq786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786 eq973
  have eq4059 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1215 X1 x
       have i₂ := eq1225 X0 x
       grind)
    | exact superpose eq1225 eq1215
    | exact resolve eq1215 eq1225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215
  have eq4060 : ∀ X0 X1 : G, (M.op X1 (σ (σ (σ (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1262 x X1
       have i₂ := eq1225 X0 x
       grind)
    | exact superpose eq1225 eq1262
    | exact resolve eq1262 eq1225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262
  have eq4837 : ∀ X0 X2 : G, (τ (τ (M.op X0 X0))) = (σ (σ (M.op X2 X2))) := by
    intro X0 X2
    first
    | (have i₁ := eq1225 X2 x
       have i₂ := eq1392 X0 x
       grind)
    | exact superpose eq1392 eq1225
    | exact resolve eq1225 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225 eq1392
  have eq6297 : ∀ X0 X1 X2 : G, (M.op X1 (σ (σ X0))) = X1 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2165 X0 X1
       have i₂ := eq12 X0 X2
       grind)
    | exact superpose eq12 eq2165
    | (have j1 := eq12 X0 X2
       grind)
    | exact resolve eq2165 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6858 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq273
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq273
    | (have j1 := eq12 (σ x) x
       grind)
    | exact resolve eq273 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq6862 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq6858
  have eq6864 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq6862
       have i₂ := eq847 x
       grind)
    | exact superpose eq847 eq6862
    | exact resolve eq6862 eq847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6862
  have eq7613 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X0) (M.op (M.op (M.op X1 X0) X1) (M.op X3 X2))) = X3 ∨ (k (M.op X0 X2) X4) = (M.op (M.op X0 X2) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq68 X2 (M.op X0 X0) X1 X3
       have i₂ := eq69 X0 X2 X4
       grind)
    | exact superpose eq69 eq68
    | (have j1 := eq69 X0 X2 X4
       grind)
    | exact resolve eq68 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq7672 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 (M.op (M.op X3 X2) (M.op (M.op X1 X0) X1)))) = X3 ∨ (k (M.op X0 X2) X4) = (M.op (M.op X0 X2) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7613 X0 X1 X2 X3 X4
       have i₂ := eq3318 (M.op X3 X2) X0 X0 (M.op (M.op X1 X0) X1)
       grind)
    | exact superpose eq3318 eq7613
    | (have j0 := eq7613 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq7613 eq3318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7613
  have eq7798 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X2) (M.op (M.op X1 X0) X1)) = X3 ∨ (k (M.op X0 X2) X4) = (M.op (M.op X0 X2) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7672 X0 X1 X2 X3 X4
       have i₂ := eq137 X0 (M.op (M.op X3 X2) (M.op (M.op X1 X0) X1))
       grind)
    | exact superpose eq137 eq7672
    | (have j0 := eq7672 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq7672 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7672
  have eq7883 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X2 (M.op X1 (M.op X1 X0)))) = X3 ∨ (k (M.op X0 X2) X4) = (M.op (M.op X0 X2) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7798 X0 X1 X2 X3 X4
       have i₂ := eq3318 X1 X3 X2 (M.op X1 X0)
       grind)
    | exact superpose eq3318 eq7798
    | (have j0 := eq7798 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq7798 eq3318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7798
  have eq7947 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X2 X0)) = X3 ∨ (k (M.op X0 X2) X4) = (M.op (M.op X0 X2) X4) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq7883 X0 x X2 X3 X4
       have i₂ := eq137 x X0
       grind)
    | exact superpose eq137 eq7883
    | (have j0 := eq7883 X0 x X2 X3 X4
       grind)
    | exact resolve eq7883 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7883
  have eq22776 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq166 X1 X2 (M.op (M.op X2 X2) X1)
       have i₂ := eq140 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq140 eq166
    | exact resolve eq166 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq25424 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2553 (σ X0) X2 X1
       have i₂ := eq847 X0
       grind)
    | exact superpose eq847 eq2553
    | exact resolve eq2553 eq847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq25517 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X3) = (M.op (M.op (M.op X0 X0) X1) (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq67 X3 (M.op X2 X1) X2
       have i₂ := eq2553 X0 X1 X2
       grind)
    | (have i₁ := eq67 X0 (M.op X1 X1) X3
       have i₂ := eq2553 X1 X3 x
       grind)
    | exact superpose eq2553 eq67
    | exact resolve eq67 eq2553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq25970 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X3) = (M.op (M.op X0 X0) (M.op X1 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25517 X0 X1 X2 X3
       have i₂ := eq3318 X2 (M.op X0 X0) X1 X3
       grind)
    | exact superpose eq3318 eq25517
    | exact resolve eq25517 eq3318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25517
  have eq26219 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X3) = (M.op X0 (M.op X0 (M.op (M.op X2 X3) X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25970 X0 X1 X2 X3
       have i₂ := eq3318 (M.op X2 X3) X0 X0 X1
       grind)
    | exact superpose eq3318 eq25970
    | exact resolve eq25970 eq3318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25970
  have eq26382 : ∀ X1 X2 X3 : G, (M.op (M.op X2 X1) X3) = (M.op (M.op X2 X3) X1) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq26219 x X1 X2 X3
       have i₂ := eq137 x (M.op (M.op X2 X3) X1)
       grind)
    | exact superpose eq137 eq26219
    | exact resolve eq26219 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26219
  have eq26648 : ∀ X0 X1 X2 X3 X4 X5 : G, (k (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X0 X2)))) (M.op X4 (M.op X0 X1))) X5) = (M.op (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X0 X2)))) (M.op X4 (M.op X0 X1))) X5) ∨ X3 = X4 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq228 X0 (M.op X0 (M.op X2 (M.op X3 (M.op X1 X2)))) X3 X3
       have i₂ := eq138 X0 X1 X2 X3
       grind)
    | exact superpose eq138 eq228
    | (have j0 := eq228 (k (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X0 X2)))) (M.op X4 (M.op X0 X1))) X5) X1 (M.op (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X0 X2)))) (M.op X4 (M.op X0 X1))) X5) X3
       grind)
    | exact resolve eq228 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq228
  have eq26858 : ∀ X0 X1 X2 X3 X4 X5 : G, (k (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X0 X2)))) (M.op X4 (M.op X0 X1))) X5) = (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X0 X2)))) (M.op X4 (M.op (M.op X0 X1) X5))) ∨ X3 = X4 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq26648 X0 X1 X2 X3 X4 X5
       have i₂ := eq498 X5 (M.op X1 (M.op X2 (M.op X3 (M.op X0 X2)))) X4 (M.op X0 X1)
       grind)
    | exact superpose eq498 eq26648
    | (have j0 := eq26648 X0 X1 X2 (k (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X0 X2)))) (M.op X4 (M.op X0 X1))) X5) (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X0 X2)))) (M.op X4 (M.op (M.op X0 X1) X5))) X5
       grind)
    | exact resolve eq26648 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26648
  have eq26932 : ∀ X0 X1 X2 X3 X4 X5 : G, (k (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X0 X2)))) (M.op X4 (M.op X0 X1))) X5) = (M.op X1 (M.op (M.op X2 (M.op X3 (M.op X0 X2))) (M.op (M.op (M.op X0 X1) X5) X4))) ∨ X3 = X4 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq26858 X0 X1 X2 X3 X4 X5
       have i₂ := eq3318 (M.op (M.op X0 X1) X5) X1 (M.op X2 (M.op X3 (M.op X0 X2))) X4
       grind)
    | exact superpose eq3318 eq26858
    | (have j0 := eq26858 X0 X1 X2 (k (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X0 X2)))) (M.op X4 (M.op X0 X1))) X5) (M.op X1 (M.op (M.op X2 (M.op X3 (M.op X0 X2))) (M.op (M.op (M.op X0 X1) X5) X4))) X5
       grind)
    | exact resolve eq26858 eq3318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26858
  have eq26994 : ∀ X0 X1 X2 X3 X4 X5 : G, (k (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X0 X2)))) (M.op X4 (M.op X0 X1))) X5) = (M.op X1 (M.op X2 (M.op (M.op X3 (M.op X0 X2)) (M.op X4 (M.op (M.op X0 X1) X5))))) ∨ X3 = X4 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq26932 X0 X1 X2 X3 X4 X5
       have i₂ := eq3318 X4 X2 (M.op X3 (M.op X0 X2)) (M.op (M.op X0 X1) X5)
       grind)
    | exact superpose eq3318 eq26932
    | (have j0 := eq26932 X0 X1 X2 (k (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X0 X2)))) (M.op X4 (M.op X0 X1))) X5) (M.op X1 (M.op X2 (M.op (M.op X3 (M.op X0 X2)) (M.op X4 (M.op (M.op X0 X1) X5))))) X5
       grind)
    | exact resolve eq26932 eq3318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26932
  have eq27034 : ∀ X0 X1 X2 X3 X4 X5 : G, (k (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X0 X2)))) (M.op X4 (M.op X0 X1))) X5) = (M.op X1 (M.op X2 (M.op X3 (M.op (M.op X0 X2) (M.op (M.op (M.op X0 X1) X5) X4))))) ∨ X3 = X4 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq26994 X0 X1 X2 X3 X4 X5
       have i₂ := eq3318 (M.op (M.op X0 X1) X5) X3 (M.op X0 X2) X4
       grind)
    | exact superpose eq3318 eq26994
    | (have j0 := eq26994 X0 X1 X2 (k (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X0 X2)))) (M.op X4 (M.op X0 X1))) X5) (M.op X1 (M.op X2 (M.op X3 (M.op (M.op X0 X2) (M.op (M.op (M.op X0 X1) X5) X4))))) X5
       grind)
    | exact resolve eq26994 eq3318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26994
  have eq27065 : ∀ X0 X1 X2 X3 X4 X5 : G, (k (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X0 X2)))) (M.op X4 (M.op X0 X1))) X5) = (M.op X1 (M.op (M.op X0 X3) (M.op (M.op (M.op X0 X1) X5) X4))) ∨ X3 = X4 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq27034 X0 X1 X2 X3 X4 X5
       have i₂ := eq3306 X0 X3 (M.op (M.op (M.op X0 X1) X5) X4) X2
       grind)
    | exact superpose eq3306 eq27034
    | (have j0 := eq27034 X0 X1 X2 (k (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X0 X2)))) (M.op X4 (M.op X0 X1))) X5) (M.op X1 (M.op (M.op X0 X3) (M.op (M.op (M.op X0 X1) X5) X4))) X5
       grind)
    | exact resolve eq27034 eq3306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27034
  have eq27089 : ∀ X0 X1 X2 X3 X4 X5 : G, (k (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X0 X2)))) (M.op X4 (M.op X0 X1))) X5) = (M.op X1 (M.op X0 (M.op X3 (M.op X4 (M.op (M.op X0 X1) X5))))) ∨ X3 = X4 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq27065 X0 X1 X2 X3 X4 X5
       have i₂ := eq3318 X4 X0 X3 (M.op (M.op X0 X1) X5)
       grind)
    | exact superpose eq3318 eq27065
    | (have j0 := eq27065 X0 X1 X2 (k (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X0 X2)))) (M.op X4 (M.op X0 X1))) X5) (M.op X1 (M.op X0 (M.op X3 (M.op X4 (M.op (M.op X0 X1) X5))))) X5
       grind)
    | exact resolve eq27065 eq3318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27065
  have eq27108 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X0 (M.op X3 (M.op X4 (M.op (M.op X0 X1) X5))))) = (k (M.op (M.op X0 X1) (M.op X4 (M.op X1 (M.op X2 (M.op X3 (M.op X0 X2)))))) X5) ∨ X3 = X4 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq27089 X0 X1 X2 X3 X4 X5
       have i₂ := eq3181 X4 (M.op X0 X1) (M.op X1 (M.op X2 (M.op X3 (M.op X0 X2))))
       grind)
    | (have i₁ := eq27089 X0 X1 X2 X3 X4 X5
       have i₂ := eq3181 X4 (M.op X1 (M.op X2 (M.op X3 (M.op X0 X2)))) (M.op X0 X1)
       grind)
    | exact superpose eq3181 eq27089
    | (have j0 := eq27089 X0 X1 X2 (M.op X1 (M.op X0 (M.op X3 (M.op X4 (M.op (M.op X0 X1) X5))))) (k (M.op (M.op X0 X1) (M.op X4 (M.op X1 (M.op X2 (M.op X3 (M.op X0 X2)))))) X5) X5
       grind)
    | exact resolve eq27089 eq3181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27089
  have eq27125 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X0 (M.op X3 (M.op X4 (M.op (M.op X0 X1) X5))))) = (k (M.op (M.op X0 (M.op X2 (M.op X3 (M.op X0 X2)))) X4) X5) ∨ X3 = X4 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq27108 X0 X1 X2 X3 X4 X5
       have i₂ := eq485 X0 X1 (M.op X2 (M.op X3 (M.op X0 X2))) X4
       grind)
    | exact superpose eq485 eq27108
    | (have j0 := eq27108 X0 X1 X2 (M.op X1 (M.op X0 (M.op X3 (M.op X4 (M.op (M.op X0 X1) X5))))) (k (M.op (M.op X0 (M.op X2 (M.op X3 (M.op X0 X2)))) X4) X5) X5
       grind)
    | exact resolve eq27108 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485 eq27108
  have eq27139 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X0 (M.op X3 (M.op X4 (M.op (M.op X0 X1) X5))))) = (k (M.op X0 (M.op X2 (M.op (M.op X3 (M.op X0 X2)) X4))) X5) ∨ X3 = X4 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq27125 X0 X1 X2 X3 X4 X5
       have i₂ := eq498 X4 X0 X2 (M.op X3 (M.op X0 X2))
       grind)
    | exact superpose eq498 eq27125
    | (have j0 := eq27125 X0 X1 X2 (M.op X1 (M.op X0 (M.op X3 (M.op X4 (M.op (M.op X0 X1) X5))))) (k (M.op X0 (M.op X2 (M.op (M.op X3 (M.op X0 X2)) X4))) X5) X5
       grind)
    | exact resolve eq27125 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27125
  have eq27152 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X0 (M.op X3 (M.op X4 (M.op (M.op X0 X1) X5))))) = (k (M.op X0 (M.op X2 (M.op X3 (M.op X0 (M.op X2 X4))))) X5) ∨ X3 = X4 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq27139 X0 X1 X2 X3 X4 X5
       have i₂ := eq498 X4 X3 X0 X2
       grind)
    | exact superpose eq498 eq27139
    | (have j0 := eq27139 X0 X1 X2 (M.op X1 (M.op X0 (M.op X3 (M.op X4 (M.op (M.op X0 X1) X5))))) (k (M.op X0 (M.op X2 (M.op X3 (M.op X0 (M.op X2 X4))))) X5) X5
       grind)
    | exact resolve eq27139 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27139
  have eq27161 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X0 (M.op X3 (M.op X4 (M.op (M.op X0 X1) X5))))) = (k (M.op X3 (M.op X2 (M.op X2 X4))) X5) ∨ X3 = X4 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq27152 X0 X1 X2 X3 X4 X5
       have i₂ := eq3132 X2 (M.op X2 X4) X0 X3
       grind)
    | exact superpose eq3132 eq27152
    | (have j0 := eq27152 X0 X1 X2 (M.op X1 (M.op X0 (M.op X3 (M.op X4 (M.op (M.op X0 X1) X5))))) (k (M.op X3 (M.op X2 (M.op X2 X4))) X5) X5
       grind)
    | exact resolve eq27152 eq3132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27152
  have eq27169 : ∀ X0 X1 X3 X4 X5 : G, (k (M.op X3 X4) X5) = (M.op X1 (M.op X0 (M.op X3 (M.op X4 (M.op (M.op X0 X1) X5))))) ∨ X3 = X4 := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq27161 X0 X1 x X3 X4 X5
       have i₂ := eq137 x X4
       grind)
    | exact superpose eq137 eq27161
    | (have j0 := eq27161 X0 X1 x (k (M.op X3 X4) X5) (M.op X1 (M.op X0 (M.op X3 (M.op X4 (M.op (M.op X0 X1) X5))))) X5
       grind)
    | exact resolve eq27161 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27161
  have eq27864 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ X1) (M.op X2 (σ (k (τ X0) X1))))) = X2 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq274 (τ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq274
    | exact resolve eq274 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq28197 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ X1) (M.op X2 (k X0 (σ X1))))) = X2 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27864 X0 X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq27864
    | (have j0 := eq27864 X0 X1 X2
       grind)
    | exact resolve eq27864 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27864
  have eq34816 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X0) = X0 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq482 X0 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq482
    | (have j1 := eq12 X0 X2
       grind)
    | exact resolve eq482 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46682 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) ≠ (M.op X1 (M.op X2 X2)) ∨ (M.op X1 (M.op X2 X2)) = (k X1 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq102 X1 (M.op X2 X2)
       have i₂ := eq22776 X2 X1 X0
       grind)
    | (have i₁ := eq102 X1 (M.op X2 X2)
       have i₂ := eq22776 X0 X1 X2
       grind)
    | exact superpose eq22776 eq102
    | (have j0 := eq102 X1 (M.op X2 X2)
       grind)
    | (have r₁ := eq102 (M.op X2 X2) (M.op X2 X2)
       have r₂ := eq22776 X2 (M.op X2 X2) X2
       grind)
    | (have r₁ := eq102 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq22776 X0 (M.op X0 X0) X0
       grind)
    | exact resolve eq102 eq22776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq46932 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) ≠ X1 ∨ (M.op X1 (M.op X2 X2)) = (k X1 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46682 X0 X1 X2
       have i₂ := eq155 X2 X1
       grind)
    | (have i₁ := eq46682 X0 X1 X2
       have i₂ := eq155 X2 (M.op X1 (M.op X2 X2))
       grind)
    | exact superpose eq155 eq46682
    | (have j0 := eq46682 X0 X1 X2
       grind)
    | (have r₁ := eq46682 (M.op X2 X2) (M.op X2 X2) X2
       have r₂ := eq155 X2 (M.op (M.op X2 X2) (M.op X2 X2))
       grind)
    | exact resolve eq46682 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46682
  have eq47429 : ∀ X1 X2 : G, (M.op X1 (M.op X2 X2)) = (k X1 (M.op X2 X2)) := by
    intro X1 X2
    first
    | (have j0 := eq46932 x X1 X2
       have j1 := eq34816 X1 X1 (M.op X2 X2)
       grind)
    | (have r₁ := eq46932 X1 x X2
       have r₂ := eq34816 x X1 X2
       grind)
    | exact resolve eq46932 eq34816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34816 eq46932
  have eq47717 : ∀ X1 X2 : G, (k X1 (M.op X2 X2)) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq47429 X1 X2
       have i₂ := eq155 X2 X1
       grind)
    | (have i₁ := eq47429 X1 X2
       have i₂ := eq155 X2 (M.op X1 (M.op X2 X2))
       grind)
    | exact superpose eq155 eq47429
    | exact resolve eq47429 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47429
  have eq49079 : ∀ X0 X1 : G, (k X1 (σ (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47717 X1 (σ (σ (M.op X0 X0)))
       have i₂ := eq2165 X0 (σ (σ (M.op X0 X0)))
       grind)
    | exact superpose eq2165 eq47717
    | exact resolve eq47717 eq2165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2165
  have eq49080 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47717 X1 (σ (σ (σ (M.op X0 X0))))
       have i₂ := eq4060 X0 (σ (σ (σ (M.op X0 X0))))
       grind)
    | exact superpose eq4060 eq47717
    | exact resolve eq47717 eq4060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4060
  have eq49083 : ∀ X0 X1 : G, (k X1 (τ (τ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47717 X1 (τ (τ (M.op X0 X0)))
       have i₂ := eq2569 X0 (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq2569 eq47717
    | exact resolve eq47717 eq2569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2569 eq47717
  have eq85772 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq6864
       grind)
    | exact superpose eq6864 eq9
    | exact resolve eq9 eq6864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6864
  have eq85857 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq85772
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq85772
    | exact resolve eq85772 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85772
  have eq85858 : x = (M.op x x) := by grind
  clear eq85857
  have eq85887 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq155 x X0
       have i₂ := eq85858
       grind)
    | exact superpose eq85858 eq155
    | exact resolve eq155 eq85858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq85890 : ∀ X0 : G, (k x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq175 x X0
       have i₂ := eq85858
       grind)
    | exact superpose eq85858 eq175
    | exact resolve eq175 eq85858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq85895 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq482 x X0 X1
       have i₂ := eq85858
       grind)
    | exact superpose eq85858 eq482
    | exact resolve eq482 eq85858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq85899 : ∀ X0 : G, (M.op X0 X0) = (τ x) := by
    intro X0
    first
    | (have i₁ := eq968 X0 x
       have i₂ := eq85858
       grind)
    | exact superpose eq85858 eq968
    | exact resolve eq968 eq85858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968
  have eq85914 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2553 x X1 X0
       have i₂ := eq85858
       grind)
    | exact superpose eq85858 eq2553
    | exact resolve eq2553 eq85858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2553
  have eq85920 : ∀ X0 : G, (τ (M.op X0 X0)) = (σ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq3437 x X0
       have i₂ := eq85858
       grind)
    | exact superpose eq85858 eq3437
    | exact resolve eq3437 eq85858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3437
  have eq85921 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq3438 x X0
       have i₂ := eq85858
       grind)
    | exact superpose eq85858 eq3438
    | exact resolve eq3438 eq85858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3438
  have eq85928 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (σ (σ x))) := by
    intro X0
    first
    | (have i₁ := eq4059 x X0
       have i₂ := eq85858
       grind)
    | exact superpose eq85858 eq4059
    | exact resolve eq4059 eq85858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4059
  have eq85936 : ∀ X0 : G, (σ (σ (M.op X0 X0))) = (τ (τ x)) := by
    intro X0
    first
    | (have i₁ := eq4837 x X0
       have i₂ := eq85858
       grind)
    | exact superpose eq85858 eq4837
    | exact resolve eq4837 eq85858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4837
  have eq85941 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22776 X0 X1 x
       have i₂ := eq85858
       grind)
    | exact superpose eq85858 eq22776
    | exact resolve eq22776 eq85858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22776 eq85858
  have eq87914 : ∀ X0 : G, x = (σ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq49079 X0 x
       have i₂ := eq85890 (σ (σ (M.op X0 X0)))
       grind)
    | exact superpose eq85890 eq49079
    | exact resolve eq49079 eq85890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49079
  have eq87915 : ∀ X0 : G, x = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq49080 X0 x
       have i₂ := eq85890 (σ (σ (σ (M.op X0 X0))))
       grind)
    | exact superpose eq85890 eq49080
    | exact resolve eq49080 eq85890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49080
  have eq87920 : ∀ X0 : G, x = (τ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq49083 X0 x
       have i₂ := eq85890 (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq85890 eq49083
    | exact resolve eq49083 eq85890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49083 eq85890
  have eq87927 : x = (τ (σ (σ x))) := by
    first
    | (have i₁ := eq87920 x
       have i₂ := eq85920 x
       grind)
    | exact superpose eq85920 eq87920
    | exact resolve eq87920 eq85920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85920 eq87920
  have eq87932 : x = (σ (τ (τ x))) := by
    first
    | (have i₁ := eq87915 x
       have i₂ := eq85936 x
       grind)
    | exact superpose eq85936 eq87915
    | exact resolve eq87915 eq85936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85936 eq87915
  have eq87933 : x = (σ (σ (σ x))) := by
    first
    | (have i₁ := eq87914 x
       have i₂ := eq85921 x
       grind)
    | exact superpose eq85921 eq87914
    | exact resolve eq87914 eq85921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87914
  have eq87969 : x = (σ x) := by
    first
    | (have i₁ := eq87927
       have i₂ := eq9 (σ x)
       grind)
    | exact superpose eq9 eq87927
    | exact resolve eq87927 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87927
  have eq87972 : x = (τ x) := by
    first
    | (have i₁ := eq87932
       have i₂ := eq10 (τ x)
       grind)
    | exact superpose eq10 eq87932
    | exact resolve eq87932 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87932
  have eq88565 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq87969
       grind)
    | exact superpose eq87969 eq14
    | exact resolve eq14 eq87969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97003 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X1 (M.op X2 X4)) (M.op X5 X3))) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X4 X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq104 (M.op X1 (M.op X2 X4)) X4 X5 X3
       have i₂ := eq104 X1 X0 X2 X4
       grind)
    | exact superpose eq104 eq104
    | exact resolve eq104 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq98385 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X1 (M.op X2 X4)) (M.op X5 X3))) = (M.op (M.op X0 X1) (M.op (M.op X0 X2) (M.op X5 X4))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq97003 X0 X1 X2 X3 X4 X5
       have i₂ := eq3318 X5 (M.op X0 X1) (M.op X0 X2) X4
       grind)
    | exact superpose eq3318 eq97003
    | exact resolve eq97003 eq3318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97003
  have eq99144 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X1 (M.op X2 X4)) (M.op X5 X3))) = (M.op X0 (M.op X1 (M.op (M.op X5 X4) (M.op X0 X2)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq98385 X0 X1 X2 X3 X4 X5
       have i₂ := eq3318 (M.op X5 X4) X0 X1 (M.op X0 X2)
       grind)
    | exact superpose eq3318 eq98385
    | exact resolve eq98385 eq3318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98385
  have eq99752 : ∀ X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X1 (M.op X2 X4)) (M.op X5 X3))) = (M.op (M.op X5 X4) (M.op X1 X2)) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq99144 x X1 X2 X3 X4 X5
       have i₂ := eq3132 X1 X2 x (M.op X5 X4)
       grind)
    | exact superpose eq3132 eq99144
    | exact resolve eq99144 eq3132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99144
  have eq100178 : ∀ X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X1 (M.op X2 X4)) (M.op X5 X3))) = (M.op X5 (M.op X4 (M.op X2 X1))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq99752 X1 X2 X3 X4 X5
       have i₂ := eq3318 X2 X5 X4 X1
       grind)
    | exact superpose eq3318 eq99752
    | exact resolve eq99752 eq3318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99752
  have eq100483 : ∀ X1 X2 X4 X5 : G, (M.op X5 (M.op X4 (M.op X2 X1))) = (M.op X5 (M.op X1 (M.op X2 X4))) := by
    intro X1 X2 X4 X5
    first
    | (have i₁ := eq100178 X4 X2 x X1 X5
       have i₂ := eq254 (M.op X4 (M.op X2 X1)) X5 x
       grind)
    | exact superpose eq254 eq100178
    | exact resolve eq100178 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100178
  have eq111063 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op (M.op (M.op X2 (M.op X3 X1)) X2) X0)) = (M.op X4 (M.op (M.op X5 (M.op X3 (M.op X4 X5))) X0)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq68 X3 X1 X2 (M.op X4 (M.op (M.op X5 (M.op X3 (M.op X4 X5))) X0))
       have i₂ := eq111 X3 X4 X5 X0
       grind)
    | exact superpose eq111 eq68
    | exact resolve eq68 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq111
  have eq111332 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op (M.op (M.op X2 (M.op X3 X1)) X2) X0)) = (M.op X4 (M.op X5 (M.op X3 (M.op (M.op X4 X5) X0)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq111063 X0 X1 X2 X3 X4 X5
       have i₂ := eq498 X0 X5 X3 (M.op X4 X5)
       grind)
    | exact superpose eq498 eq111063
    | exact resolve eq111063 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111063
  have eq111873 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op (M.op X2 (M.op X3 X1)) X2) X0)) = (M.op X4 (M.op (M.op X4 X3) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq111332 X0 X1 X2 X3 X4 x
       have i₂ := eq3306 X4 X3 X0 x
       grind)
    | exact superpose eq3306 eq111332
    | exact resolve eq111332 eq3306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3306 eq111332
  have eq112374 : ∀ X0 X1 X3 X4 : G, (M.op X4 (M.op (M.op X4 X3) X0)) = (M.op X1 (M.op (M.op x (M.op X3 X1)) X0)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq111873 X0 X1 x X3 X4
       have i₂ := eq85914 x (M.op X3 X1)
       grind)
    | exact superpose eq85914 eq111873
    | exact resolve eq111873 eq85914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111873
  have eq112816 : ∀ X0 X1 X3 X4 : G, (M.op X4 (M.op (M.op X4 X3) X0)) = (M.op X1 (M.op x (M.op X3 (M.op X1 X0)))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq112374 X0 X1 X3 X4
       have i₂ := eq498 X0 x X3 X1
       grind)
    | exact superpose eq498 eq112374
    | exact resolve eq112374 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112374
  have eq113163 : ∀ X0 X3 X4 : G, (M.op X4 (M.op (M.op X4 X3) X0)) = (M.op X3 (M.op x X0)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq112816 X0 x X3 X4
       have i₂ := eq3132 x X0 x X3
       grind)
    | exact superpose eq3132 eq112816
    | exact resolve eq112816 eq3132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112816
  have eq115152 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) X4) = (M.op X1 (M.op X2 (M.op (M.op (M.op X3 (M.op X4 X2)) X3) X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq235 X4 X1 (M.op X2 (M.op (M.op (M.op X3 (M.op X4 X2)) X3) X0))
       have i₂ := eq112 X4 X2 X3 X0
       grind)
    | exact superpose eq112 eq235
    | exact resolve eq235 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq235
  have eq115318 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 X0) X4) = (M.op X1 (M.op X2 (M.op (M.op x (M.op X4 X2)) X0))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq115152 X0 X1 X2 x X4
       have i₂ := eq85914 x (M.op X4 X2)
       grind)
    | exact superpose eq85914 eq115152
    | exact resolve eq115152 eq85914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115152
  have eq115872 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 X0) X4) = (M.op X1 (M.op X2 (M.op x (M.op X4 (M.op X2 X0))))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq115318 X0 X1 X2 X4
       have i₂ := eq498 X0 x X4 X2
       grind)
    | exact superpose eq498 eq115318
    | exact resolve eq115318 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498 eq115318
  have eq116403 : ∀ X0 X1 X4 : G, (M.op (M.op X1 X0) X4) = (M.op X1 (M.op X4 (M.op x X0))) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq115872 X0 X1 x X4
       have i₂ := eq3132 x X0 x X4
       grind)
    | exact superpose eq3132 eq115872
    | exact resolve eq115872 eq3132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3132 eq115872
  have eq375780 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq309 X0 X1 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq378590 : ∀ X0 X1 X2 : G, X0 ≠ X2 ∨ (k (M.op X1 (M.op (M.op X1 X2) X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq375780 (M.op X1 (M.op (M.op X1 X2) X0)) X2
       have i₂ := eq252 X2 X1 X0
       grind)
    | exact superpose eq252 eq375780
    | (have j0 := eq375780 (M.op X1 (M.op (M.op X1 X2) X0)) X2
       grind)
    | (have r₁ := eq375780 (M.op X1 (M.op (M.op X1 X2) X2)) X2
       have r₂ := eq252 X2 X1 X2
       grind)
    | exact resolve eq375780 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq375780
  have eq378660 : ∀ X0 X2 : G, X0 ≠ X2 ∨ (k (M.op X2 (M.op x X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq378590 X0 x X2
       have i₂ := eq113163 X0 X2 x
       grind)
    | exact superpose eq113163 eq378590
    | (have j0 := eq378590 X0 x X2
       grind)
    | (have r₁ := eq378590 (M.op x (M.op (M.op x x) X0)) x (M.op x (M.op x X0))
       have r₂ := eq113163 X0 x x
       grind)
    | (have r₁ := eq378590 (M.op x (M.op x X0)) x (M.op x (M.op (M.op x x) X0))
       have r₂ := eq113163 X0 x x
       grind)
    | exact resolve eq378590 eq113163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113163 eq378590
  have eq380162 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op x (σ y)) ∨ (M.op (M.op y x) X1) = (k (M.op y x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq88565
       have i₂ := eq718 y x X0 X1
       grind)
    | exact superpose eq718 eq88565
    | (have j1 := eq718 y x x X1
       grind)
    | exact resolve eq88565 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq380855 : ∀ X1 : G, (σ (σ x)) ≠ (M.op x (σ y)) ∨ (M.op (M.op y x) X1) = (k (M.op y x) X1) := by
    intro X1
    first
    | (have i₁ := eq380162 x X1
       have i₂ := eq85921 x
       grind)
    | exact superpose eq85921 eq380162
    | (have j0 := eq380162 x X1
       grind)
    | exact resolve eq380162 eq85921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85921 eq380162
  have eq381119 : ∀ X1 : G, (σ x) ≠ (M.op x (σ y)) ∨ (M.op (M.op y x) X1) = (k (M.op y x) X1) := by
    intro X1
    first
    | (have i₁ := eq380855 X1
       have i₂ := eq87969
       grind)
    | exact superpose eq87969 eq380855
    | (have j0 := eq380855 X1
       grind)
    | exact resolve eq380855 eq87969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380855
  have eq381314 : ∀ X1 : G, x ≠ (M.op x (σ y)) ∨ (M.op (M.op y x) X1) = (k (M.op y x) X1) := by
    intro X1
    first
    | (have i₁ := eq381119 X1
       have i₂ := eq87969
       grind)
    | exact superpose eq87969 eq381119
    | (have j0 := eq381119 X1
       grind)
    | exact resolve eq381119 eq87969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381119
  have eq381437 : ∀ X1 : G, (M.op y X1) = (k y X1) ∨ x ≠ (M.op x (σ y)) := by
    intro X1
    first
    | (have i₁ := eq381314 X1
       have i₂ := eq85887 y
       grind)
    | exact superpose eq85887 eq381314
    | exact resolve eq381314 eq85887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381314
  have eq381504 : ∀ X1 : G, (M.op y X1) = (k y X1) := by
    intro X1
    first
    | (have j0 := eq381437 X1
       have j1 := eq2157 y X1 X1
       grind)
    | (have r₁ := eq381437 X1
       have r₂ := eq2157 y x x
       grind)
    | exact resolve eq381437 eq2157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2157 eq381437
  have eq388883 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) X2) = (M.op (M.op X1 X2) X1) ∨ (k X0 X3) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25424 X0 X1 X2
       have i₂ := eq157 X0 X0 X3
       grind)
    | exact superpose eq157 eq25424
    | (have j1 := eq157 X0 X1 X3
       grind)
    | exact resolve eq25424 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq25424
  have eq390653 : ∀ X0 X2 X3 : G, (M.op (σ X0) X2) = (M.op x X2) ∨ (k X0 X3) = (M.op X0 X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq388883 X0 x X2 X3
       have i₂ := eq85914 x X2
       grind)
    | exact superpose eq85914 eq388883
    | (have j0 := eq388883 X0 x X2 X3
       grind)
    | exact resolve eq388883 eq85914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388883
  have eq416113 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (k X0 (σ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28197 X0 X1 (σ X1)
       have i₂ := eq137 (σ X1) (k X0 (σ X1))
       grind)
    | exact superpose eq137 eq28197
    | (have j0 := eq28197 X0 X1 x
       grind)
    | exact resolve eq28197 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28197
  have eq416584 : ∀ X0 X1 : G, (τ x) = X0 ∨ (σ X1) = (M.op X0 (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq416113 X0 X1
       have i₂ := eq85899 X0
       grind)
    | exact superpose eq85899 eq416113
    | (have j0 := eq416113 X0 X1
       grind)
    | exact resolve eq416113 eq85899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416113
  have eq416731 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (k X0 (σ X1))) ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq416584 X0 X1
       have i₂ := eq87972
       grind)
    | exact superpose eq87972 eq416584
    | (have j0 := eq416584 X0 X1
       grind)
    | exact resolve eq416584 eq87972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416584
  have eq416975 : ∀ X0 X1 : G, (M.op X1 (k X1 X0)) = X0 ∨ x = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq416731 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq416731
    | (have j0 := eq416731 X1 X1
       grind)
    | exact resolve eq416731 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416731
  have eq420216 : ∀ X0 X1 : G, (M.op x X0) = (M.op (k X1 X0) X1) ∨ x = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq85895 (k X1 X0) X1
       have i₂ := eq416975 X0 X1
       grind)
    | exact superpose eq416975 eq85895
    | (have j1 := eq416975 X0 X1
       grind)
    | exact resolve eq85895 eq416975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427129 : ∀ X0 : G, (k (M.op X0 (M.op x X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq378660 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378660
  have eq433837 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (M.op x (σ X0)))) X0) := by
    intro X0
    first
    | (have i₁ := eq20 (M.op (σ X0) (M.op x (σ X0))) X0
       have i₂ := eq427129 (σ X0)
       grind)
    | exact superpose eq427129 eq20
    | exact resolve eq20 eq427129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq433848 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (M.op x (τ X0)))) X0) := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op (τ X0) (M.op x (τ X0)))
       have i₂ := eq427129 (τ X0)
       grind)
    | exact superpose eq427129 eq16
    | exact resolve eq16 eq427129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq427129
  have eq433866 : ∀ X0 : G, (k (σ (M.op (τ X0) (M.op x (τ X0)))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq433848 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq433848
    | exact resolve eq433848 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433848
  have eq433876 : ∀ X0 : G, (k (τ (M.op (σ X0) (M.op x (σ X0)))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq433837 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq433837
    | exact resolve eq433837 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433837
  have eq443173 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op (k X2 X0) (M.op x X0))) ∨ x = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq140 X1 (k X2 X0) X2
       have i₂ := eq420216 X0 X2
       grind)
    | exact superpose eq420216 eq140
    | (have j1 := eq420216 X0 X2
       grind)
    | exact resolve eq140 eq420216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq420216
  have eq443428 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 (M.op x (k X2 X0)))) ∨ x = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq443173 X0 X1 X2
       have i₂ := eq100483 X0 x (k X2 X0) X2
       grind)
    | (have i₁ := eq443173 X0 X1 X2
       have i₂ := eq100483 (k X2 X0) x X0 X2
       grind)
    | exact superpose eq100483 eq443173
    | (have j0 := eq443173 X0 X1 X2
       grind)
    | exact resolve eq443173 eq100483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100483 eq443173
  have eq443602 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X2 (k X2 X0)) X0) ∨ x = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq443428 X0 X1 X2
       have i₂ := eq116403 (k X2 X0) X2 X0
       grind)
    | exact superpose eq116403 eq443428
    | (have j0 := eq443428 X0 X1 X2
       grind)
    | exact resolve eq443428 eq116403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116403 eq443428
  have eq443721 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X2 X0) (k X2 X0)) ∨ x = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq443602 X0 X1 X2
       have i₂ := eq26382 (k X2 X0) X2 X0
       grind)
    | (have i₁ := eq443602 X0 X1 X2
       have i₂ := eq26382 X0 X2 (k X2 X0)
       grind)
    | exact superpose eq26382 eq443602
    | (have j0 := eq443602 X0 X1 X2
       grind)
    | exact resolve eq443602 eq26382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443602
  have eq443804 : ∀ X0 X2 : G, (τ x) = (M.op (M.op X2 X0) (k X2 X0)) ∨ x = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq443721 X0 x X2
       have i₂ := eq85899 x
       grind)
    | exact superpose eq85899 eq443721
    | (have j0 := eq443721 X0 x X2
       grind)
    | exact resolve eq443721 eq85899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443721
  have eq443854 : ∀ X0 X2 : G, x = (M.op (M.op X2 X0) (k X2 X0)) ∨ x = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq443804 X0 X2
       have i₂ := eq87972
       grind)
    | exact superpose eq87972 eq443804
    | (have j0 := eq443804 X0 (M.op (M.op X2 X0) (k X2 X0))
       grind)
    | exact resolve eq443804 eq87972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443804
  have eq488728 : ∀ X0 X1 : G, x = (M.op X0 (k X1 (k X1 X0))) ∨ x = X1 ∨ x = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq443854 (k X1 X0) X1
       have i₂ := eq416975 X0 X1
       grind)
    | exact superpose eq416975 eq443854
    | (have j0 := eq443854 X0 (M.op X0 (k X1 (k X1 X0)))
       have j1 := eq416975 X0 (M.op X0 (k X1 (k X1 X0)))
       grind)
    | exact resolve eq443854 eq416975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443854
  have eq489072 : ∀ X0 X1 : G, x = (M.op X0 (k X1 (k X1 X0))) ∨ x = X1 := by
    intro X0 X1
    first
    | (have j0 := eq488728 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488728
  have eq555286 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X0 ∨ (k (M.op (τ X0) x) X1) = (M.op (M.op (τ X0) x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq433866 X0
       have i₂ := eq7947 (τ X0) x (τ X0) X1
       grind)
    | exact superpose eq7947 eq433866
    | (have j1 := eq7947 (τ X0) x x X1
       grind)
    | exact resolve eq433866 eq7947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7947 eq433866
  have eq555356 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k (M.op (τ X0) x) X1) = (M.op (M.op (τ X0) x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq555286 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq555286
    | (have j0 := eq555286 X0 X1
       grind)
    | exact resolve eq555286 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555286
  have eq555418 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (M.op (τ X0) x) X1) = (M.op (M.op (τ X0) x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq555356 X0 X1
       have i₂ := eq809 X0
       grind)
    | exact superpose eq809 eq555356
    | (have j0 := eq555356 X0 X1
       grind)
    | exact resolve eq555356 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809 eq555356
  have eq555457 : ∀ X0 X1 : G, (τ x) = X0 ∨ (k (M.op (τ X0) x) X1) = (M.op (M.op (τ X0) x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq555418 X0 X1
       have i₂ := eq85899 X0
       grind)
    | exact superpose eq85899 eq555418
    | (have j0 := eq555418 X0 X1
       grind)
    | exact resolve eq555418 eq85899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85899 eq555418
  have eq555484 : ∀ X0 X1 : G, x = X0 ∨ (k (M.op (τ X0) x) X1) = (M.op (M.op (τ X0) x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq555457 X0 X1
       have i₂ := eq87972
       grind)
    | exact superpose eq87972 eq555457
    | (have j0 := eq555457 X0 X1
       grind)
    | exact resolve eq555457 eq87972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87972 eq555457
  have eq555506 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq555484 X0 X1
       have i₂ := eq85887 (τ X0)
       grind)
    | exact superpose eq85887 eq555484
    | (have j0 := eq555484 X0 X1
       grind)
    | exact resolve eq555484 eq85887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555484
  have eq559057 : ∀ X0 X1 : G, (M.op X0 x) = (k X1 (k X1 X0)) ∨ x = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq137 X0 (k X1 (k X1 X0))
       have i₂ := eq489072 X0 X1
       grind)
    | exact superpose eq489072 eq137
    | (have j1 := eq489072 X0 X1
       grind)
    | exact resolve eq137 eq489072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489072
  have eq559318 : ∀ X0 X1 : G, (k X1 (k X1 X0)) = X0 ∨ x = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq559057 X0 X1
       have i₂ := eq85887 X0
       grind)
    | exact superpose eq85887 eq559057
    | (have j0 := eq559057 X0 X1
       grind)
    | exact resolve eq559057 eq85887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559057
  have eq560612 : ∀ X0 X1 : G, (σ (k X1 (k X1 (τ X0)))) = X0 ∨ (σ X1) = x := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 X0 X1
       have i₂ := eq559318 X0 (σ X1)
       grind)
    | exact superpose eq559318 eq26
    | (have j1 := eq559318 X0 (σ X1)
       grind)
    | exact resolve eq26 eq559318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq559318
  have eq842902 : ∀ X0 X1 : G, (σ (k (τ X0) (M.op (τ X0) (τ X1)))) = X1 ∨ (σ (τ X0)) = x ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq560612 X1 (τ X0)
       have i₂ := eq555506 X0 (τ X1)
       grind)
    | exact superpose eq555506 eq560612
    | (have j0 := eq560612 X0 (τ X0)
       have j1 := eq555506 (σ (τ X0)) X1
       grind)
    | exact resolve eq560612 eq555506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555506 eq560612
  have eq843021 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) (τ X1)))) = X1 ∨ (σ (τ X0)) = x ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq842902 X0 X1
       have i₂ := eq15 X0 (M.op (τ X0) (τ X1))
       grind)
    | exact superpose eq15 eq842902
    | (have j0 := eq842902 X0 X1
       grind)
    | exact resolve eq842902 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq842902
  have eq843112 : ∀ X0 X1 : G, x = X0 ∨ (k X0 (σ (M.op (τ X0) (τ X1)))) = X1 ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq843021 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq843021
    | (have j0 := eq843021 X0 X1
       grind)
    | exact resolve eq843021 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843021
  have eq843113 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) (τ X1)))) = X1 ∨ x = X0 := by
    intro X0 X1
    first
    | (have j0 := eq843112 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843112
  have eq882220 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ x = X1 ∨ x = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq416975 (σ (M.op (τ X1) (τ X0))) X1
       have i₂ := eq843113 X1 X0
       grind)
    | exact superpose eq843113 eq416975
    | (have j0 := eq416975 X0 X1
       have j1 := eq843113 X1 X1
       grind)
    | exact resolve eq416975 eq843113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416975 eq843113
  have eq882300 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ x = X1 := by
    intro X0 X1
    first
    | (have j0 := eq882220 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882220
  have eq963630 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X3 (M.op X0 (k (M.op X0 X1) X2)))) = X1 ∨ X0 = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2937 X3 (M.op X3 X2) X0 X2 X1
       have i₂ := eq27169 X3 X2 X0 X1 X2
       grind)
    | exact superpose eq27169 eq2937
    | (have j1 := eq27169 X0 X1 (M.op (M.op X3 X2) (M.op X3 (M.op X0 (k (M.op X0 X1) X2)))) X1 x
       grind)
    | exact resolve eq2937 eq27169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2937 eq27169
  have eq964247 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 (M.op (M.op X0 (k (M.op X0 X1) X2)) X3))) = X1 ∨ X0 = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq963630 X0 X1 X2 X3
       have i₂ := eq3318 (M.op X0 (k (M.op X0 X1) X2)) X3 X2 X3
       grind)
    | exact superpose eq3318 eq963630
    | (have j0 := eq963630 (M.op X3 (M.op X2 (M.op (M.op X0 (k (M.op X0 X1) X2)) X3))) X1 X2 X3
       grind)
    | exact resolve eq963630 eq3318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3318 eq963630
  have eq964271 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (k (M.op X0 X1) X2)) X2) = X1 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq964247 X0 X1 X2 x
       have i₂ := eq254 X2 (M.op X0 (k (M.op X0 X1) X2)) x
       grind)
    | exact superpose eq254 eq964247
    | (have j0 := eq964247 (M.op (M.op X0 (k (M.op X0 X1) X2)) X2) X1 X2 x
       grind)
    | exact resolve eq964247 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254 eq964247
  have eq964279 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (k (M.op X0 X1) X2)) = X1 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq964271 X0 X1 X2
       have i₂ := eq26382 (k (M.op X0 X1) X2) X0 X2
       grind)
    | (have i₁ := eq964271 X0 X1 X2
       have i₂ := eq26382 X2 X0 (k (M.op X0 X1) X2)
       grind)
    | exact superpose eq26382 eq964271
    | (have j0 := eq964271 (M.op (M.op X0 X2) (k (M.op X0 X1) X2)) X1 X2
       grind)
    | exact resolve eq964271 eq26382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26382 eq964271
  have eq1087101 : ∀ X0 X1 : G, (M.op x (k (M.op X1 X0) X1)) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq85941 X1 (k (M.op X1 X0) X1)
       have i₂ := eq964279 X1 X0 X1
       grind)
    | exact superpose eq964279 eq85941
    | (have j1 := eq964279 (M.op x (k (M.op X1 X0) X1)) X0 x
       grind)
    | exact resolve eq85941 eq964279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85941 eq964279
  have eq1505609 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (k (τ X0) X2) = (M.op (τ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6297 (τ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6297
    | (have j0 := eq6297 (τ X0) X1 X2
       grind)
    | exact resolve eq6297 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6297
  have eq2221642 : ∀ X0 X1 : G, (σ (σ (σ x))) = (σ (M.op x (σ X0))) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq85928 (σ X0)
       have i₂ := eq390653 X0 (σ X0) X1
       grind)
    | exact superpose eq390653 eq85928
    | (have j1 := eq390653 X0 x X1
       grind)
    | exact resolve eq85928 eq390653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85928 eq390653
  have eq2221728 : ∀ X0 X1 : G, x = (σ (M.op x (σ X0))) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2221642 X0 X1
       have i₂ := eq87933
       grind)
    | exact superpose eq87933 eq2221642
    | (have j0 := eq2221642 X0 X1
       grind)
    | exact resolve eq2221642 eq87933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87933 eq2221642
  have eq2229190 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ x = (σ (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2221728 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2221728
    | (have j0 := eq2221728 (τ X0) X1
       grind)
    | exact resolve eq2221728 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2221728
  have eq2598811 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (k (τ y) X0) = (M.op (τ y) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq1505609 y (σ x) X0
       grind)
    | exact superpose eq1505609 eq14
    | (have j1 := eq1505609 y x X0
       grind)
    | exact resolve eq14 eq1505609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1505609
  have eq2598842 : ∀ X0 : G, x ≠ (σ (M.op x y)) ∨ (k (τ y) X0) = (M.op (τ y) X0) := by
    intro X0
    first
    | (have i₁ := eq2598811 X0
       have i₂ := eq87969
       grind)
    | exact superpose eq87969 eq2598811
    | (have j0 := eq2598811 X0
       grind)
    | exact resolve eq2598811 eq87969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2598811
  have eq2598888 : ∀ X0 : G, (k (τ y) X0) = (M.op (τ y) X0) := by
    intro X0
    first
    | (have j0 := eq2598842 X0
       have j1 := eq2229190 y X0
       grind)
    | (have r₁ := eq2598842 X0
       have r₂ := eq2229190 y x
       grind)
    | exact resolve eq2598842 eq2229190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2229190 eq2598842
  have eq2599149 : ∀ X0 : G, (τ (k y X0)) = (M.op (τ y) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 y
       have i₂ := eq2598888 (τ X0)
       grind)
    | exact superpose eq2598888 eq31
    | exact resolve eq31 eq2598888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2598888
  have eq2599591 : ∀ X0 : G, (τ (M.op y X0)) = (M.op (τ y) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2599149 X0
       have i₂ := eq381504 X0
       grind)
    | exact superpose eq381504 eq2599149
    | exact resolve eq2599149 eq381504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2599149
  have eq2600362 : ∀ X0 : G, (M.op x (τ X0)) = (M.op (τ (M.op y X0)) (τ y)) := by
    intro X0
    first
    | (have i₁ := eq85914 (τ y) (τ X0)
       have i₂ := eq2599591 X0
       grind)
    | exact superpose eq2599591 eq85914
    | exact resolve eq85914 eq2599591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2599591
  have eq2611942 : ∀ X0 : G, (σ (M.op x (τ X0))) = (M.op (M.op y X0) y) ∨ x = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq882300 y (M.op y X0)
       have i₂ := eq2600362 X0
       grind)
    | exact superpose eq2600362 eq882300
    | (have j0 := eq882300 X0 (M.op y X0)
       grind)
    | exact resolve eq882300 eq2600362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882300 eq2600362
  have eq2611999 : ∀ X0 : G, (M.op x X0) = (σ (M.op x (τ X0))) ∨ x = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq2611942 X0
       have i₂ := eq85914 y X0
       grind)
    | exact superpose eq85914 eq2611942
    | (have j0 := eq2611942 X0
       grind)
    | exact resolve eq2611942 eq85914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2611942
  have eq2624116 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) ∨ x = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2611999 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2611999
    | (have j0 := eq2611999 (σ X0)
       grind)
    | exact resolve eq2611999 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2611999
  have eq3359473 : (M.op x (σ y)) ≠ (M.op x (σ y)) ∨ x = (M.op y (σ y)) := by
    first
    | (have i₁ := eq88565
       have i₂ := eq2624116 y
       grind)
    | exact superpose eq2624116 eq88565
    | (have j1 := eq2624116 y
       grind)
    | (have r₁ := eq88565
       have r₂ := eq2624116 y
       grind)
    | exact resolve eq88565 eq2624116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88565 eq2624116
  have eq3359499 : x = (M.op y (σ y)) := by grind
  clear eq3359473
  have eq3359665 : (σ y) = (M.op y x) := by
    first
    | (have i₁ := eq137 y (σ y)
       have i₂ := eq3359499
       grind)
    | exact superpose eq3359499 eq137
    | exact resolve eq137 eq3359499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq3359676 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op x (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq253 (σ y) y X0
       have i₂ := eq3359499
       grind)
    | exact superpose eq3359499 eq253
    | exact resolve eq253 eq3359499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq3359800 : (M.op x y) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq85914 y (σ y)
       have i₂ := eq3359499
       grind)
    | exact superpose eq3359499 eq85914
    | exact resolve eq85914 eq3359499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85914 eq3359499
  have eq3360625 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq3359676 X0
       have i₂ := eq85895 X0 y
       grind)
    | exact superpose eq85895 eq3359676
    | exact resolve eq3359676 eq85895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85895 eq3359676
  have eq3360636 : y = (σ y) := by
    first
    | (have i₁ := eq3359665
       have i₂ := eq85887 y
       grind)
    | exact superpose eq85887 eq3359665
    | exact resolve eq3359665 eq85887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85887 eq3359665
  have eq3361368 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq3360636
       grind)
    | exact superpose eq3360636 eq14
    | exact resolve eq14 eq3360636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3361421 : ∀ X0 : G, (k y (τ X0)) = (τ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq28 y X0
       have i₂ := eq3360636
       grind)
    | exact superpose eq3360636 eq28
    | exact resolve eq28 eq3360636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq3362087 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq3361421 X0
       have i₂ := eq381504 X0
       grind)
    | exact superpose eq381504 eq3361421
    | exact resolve eq3361421 eq381504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3361421
  have eq3362106 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq3361368
       have i₂ := eq87969
       grind)
    | exact superpose eq87969 eq3361368
    | exact resolve eq3361368 eq87969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87969 eq3361368
  have eq3362219 : ∀ X0 : G, (M.op y (τ X0)) = (τ (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq3362087 X0
       have i₂ := eq381504 (τ X0)
       grind)
    | exact superpose eq381504 eq3362087
    | exact resolve eq3362087 eq381504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381504 eq3362087
  have eq3378434 : y = (k (τ (M.op (σ y) (M.op x y))) y) := by
    first
    | (have i₁ := eq433876 y
       have i₂ := eq3359800
       grind)
    | exact superpose eq3359800 eq433876
    | exact resolve eq433876 eq3359800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433876 eq3359800
  have eq3379282 : y = (k (τ (M.op y (M.op x (σ y)))) y) := by
    first
    | (have i₁ := eq3378434
       have i₂ := eq3181 x y (σ y)
       grind)
    | (have i₁ := eq3378434
       have i₂ := eq3181 x (σ y) y
       grind)
    | exact superpose eq3181 eq3378434
    | exact resolve eq3378434 eq3181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3181 eq3378434
  have eq3379471 : y = (k (M.op y (τ (M.op x (σ y)))) y) := by
    first
    | (have i₁ := eq3379282
       have i₂ := eq3362219 (M.op x (σ y))
       grind)
    | exact superpose eq3362219 eq3379282
    | exact resolve eq3379282 eq3362219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3362219 eq3379282
  have eq3379588 : y = (k (M.op y (τ (M.op x y))) y) := by
    first
    | (have i₁ := eq3379471
       have i₂ := eq3360625 x
       grind)
    | exact superpose eq3360625 eq3379471
    | exact resolve eq3379471 eq3360625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3360625 eq3379471
  have eq3476142 : (M.op x y) = (τ (M.op x y)) ∨ y = (τ (M.op x y)) := by
    first
    | (have i₁ := eq1087101 (τ (M.op x y)) y
       have i₂ := eq3379588
       grind)
    | exact superpose eq3379588 eq1087101
    | (have j0 := eq1087101 (M.op x y) (τ (M.op x y))
       grind)
    | exact resolve eq1087101 eq3379588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087101 eq3379588
  have eq3904768 : (M.op x y) = (σ (M.op x y)) ∨ y = (τ (M.op x y)) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq3476142
       grind)
    | exact superpose eq3476142 eq10
    | exact resolve eq10 eq3476142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3476142
  have eq3904771 : y = (τ (M.op x y)) := by
    first
    | (have r₁ := eq3904768
       have r₂ := eq3362106
       grind)
    | exact resolve eq3904768 eq3362106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3904768
  have eq3904842 : (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq3904771
       grind)
    | exact superpose eq3904771 eq10
    | exact resolve eq10 eq3904771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3904771
  have eq3905152 : y = (M.op x y) := by
    first
    | (have i₁ := eq3904842
       have i₂ := eq3360636
       grind)
    | exact superpose eq3360636 eq3904842
    | exact resolve eq3904842 eq3360636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3904842
  have eq3905324 : y ≠ (σ y) := by
    first
    | (have i₁ := eq3362106
       have i₂ := eq3905152
       grind)
    | exact superpose eq3905152 eq3362106
    | exact resolve eq3362106 eq3905152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3362106 eq3905152
  have eq3906168 : False := by grind
  exact eq3906168

/-- `Equation543`: `x = y ◇ (z ◇ (x ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation543 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law543 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law543.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X0 (M.op X1 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 (M.op X0 (M.op X1 X2))) (M.op X3 X0))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X1 (M.op X2 (M.op X0 (M.op X1 X2)))
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 (M.op X2 X1)) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 X1 (M.op X0 (M.op X2 X1))
       have i₂ := eq8 X0 X2 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq28 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X2 X0))) = X2 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 X1 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X1 X2)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq46 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X1 (M.op X0 X2)) X1
       have i₂ := eq19 X1 X2 X0
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq117 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X2 X1))) = X2 ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X1 X0 X1 X2
       have i₂ := eq28 X1 X1 X0
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 X1 X0 X2
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq182 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 x X0 X1 X1
       have i₂ := eq46 x X1 (M.op X0 X1)
       grind)
    | exact superpose eq46 eq18
    | exact resolve eq18 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq46
  have eq214 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq30 x y
       grind)
    | exact superpose eq30 eq14
    | (have j1 := eq30 x y
       grind)
    | exact resolve eq14 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq279 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 X1
       have i₂ := eq182 X1 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq182 eq8
    | exact resolve eq8 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq341 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq182 X0 (M.op X1 X1)
       have i₂ := eq279 X0 X1
       grind)
    | exact superpose eq279 eq182
    | exact resolve eq182 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq705 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X1 (M.op X0 X0)
       have i₂ := eq463 X0 (σ X1)
       grind)
    | exact superpose eq463 eq38
    | exact resolve eq38 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq706 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0)
       have i₂ := eq463 X0 (τ X1)
       grind)
    | exact superpose eq463 eq16
    | exact resolve eq16 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq13223 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X2 ∨ (M.op X0 X0) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq117 X0 X0 X0
       have i₂ := eq341 X0 X1
       grind)
    | (have i₁ := eq117 X0 X1 X1
       have i₂ := eq341 X0 X1
       grind)
    | exact superpose eq341 eq117
    | exact resolve eq117 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq13556 : ∀ X0 X2 : G, (M.op X0 X0) = (k X2 X2) ∨ (M.op X0 X0) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq13223 X0 x X2
       have i₂ := eq182 x (M.op X0 X0)
       grind)
    | exact superpose eq182 eq13223
    | (have j0 := eq13223 X0 x X2
       grind)
    | exact resolve eq13223 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13223
  have eq14658 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq341 X1 X2
       have i₂ := eq13556 X2 X0
       grind)
    | exact superpose eq13556 eq341
    | (have j1 := eq13556 X1 X0
       grind)
    | exact resolve eq341 eq13556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14770 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq706 X1 (σ (M.op X1 X1))
       have i₂ := eq13556 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq13556 eq706
    | (have j1 := eq13556 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq706 eq13556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq14772 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq705 X1 (τ (M.op X1 X1))
       have i₂ := eq13556 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq13556 eq705
    | (have j1 := eq13556 X0 (τ (M.op X1 X1))
       grind)
    | exact resolve eq705 eq13556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq14782 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13556 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14785 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq14772 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14772
  have eq14786 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq14770 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14770
  have eq15298 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq182 X1 X1
       have i₂ := eq14785 X1 X0
       grind)
    | exact superpose eq14785 eq182
    | exact resolve eq182 eq14785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq15722 : ∀ X0 X2 : G, (σ (M.op X0 X0)) = (τ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq14785 x X2
       have i₂ := eq14786 x X0
       grind)
    | exact superpose eq14786 eq14785
    | exact resolve eq14785 eq14786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14785 eq14786
  have eq16318 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq214
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq214
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq214 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq16319 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq16318
  have eq38175 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14782 X1 X0
       have i₂ := eq27 X0 X0
       grind)
    | exact superpose eq27 eq14782
    | (have j0 := eq14782 X1 X0
       have j1 := eq27 X0 X0
       grind)
    | (have r₁ := eq14782 X0 X0
       have r₂ := eq27 X0 X0
       grind)
    | exact resolve eq14782 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq38191 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq38175 X0 X1
       have j1 := eq14782 X1 X0
       grind)
    | (have r₁ := eq38175 X1 X1
       have r₂ := eq14782 X1 X1
       grind)
    | (have r₁ := eq38175 (M.op X0 X0) X1
       have r₂ := eq14782 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | (have r₁ := eq38175 (k (M.op X1 X1) (M.op X1 X1)) X1
       have r₂ := eq14782 X0 (M.op X1 X1)
       grind)
    | exact resolve eq38175 eq14782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14782 eq38175
  have eq38311 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38191 X1 X2
       have i₂ := eq341 X1 X0
       grind)
    | (have i₁ := eq38191 X1 X2
       have i₂ := eq341 X0 X1
       grind)
    | exact superpose eq341 eq38191
    | (have j0 := eq38191 X1 X2
       grind)
    | (have r₁ := eq38191 (M.op X1 X1) X1
       have r₂ := eq341 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq38191 (M.op X0 X0) X1
       have r₂ := eq341 X0 (M.op X0 X0)
       grind)
    | exact resolve eq38191 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341 eq38191
  have eq91292 : ∀ X0 X2 X3 : G, (k X2 X0) = X0 ∨ (k X0 X0) = (M.op X3 X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq463 X2 x
       have i₂ := eq14658 X0 x X2
       grind)
    | (have i₁ := eq463 X0 x
       have i₂ := eq14658 (M.op X0 X0) x X2
       grind)
    | exact superpose eq14658 eq463
    | (have j1 := eq14658 X0 X3 X2
       grind)
    | exact resolve eq463 eq14658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463 eq14658
  have eq95390 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq91292 X0 x X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91292
  have eq95397 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq95390 X0 X1
       have j1 := eq13556 X1 X0
       grind)
    | (have r₁ := eq95390 (k x x) X0
       have r₂ := eq13556 X0 x
       grind)
    | (have r₁ := eq95390 x X0
       have r₂ := eq13556 X0 x
       grind)
    | (have r₁ := eq95390 (M.op X0 X0) X1
       have r₂ := eq13556 X0 (M.op X1 X1)
       grind)
    | exact resolve eq95390 eq13556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13556 eq95390
  have eq96228 : ∀ X0 X2 : G, (σ (k X0 X0)) = (τ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq15722 x X2
       have i₂ := eq95397 X0 x
       grind)
    | exact superpose eq95397 eq15722
    | exact resolve eq15722 eq95397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15722
  have eq96269 : ∀ X0 X2 X3 : G, (k X0 X0) ≠ X2 ∨ (M.op X3 X3) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq38311 x X2 X3
       have i₂ := eq95397 X0 x
       grind)
    | exact superpose eq95397 eq38311
    | (have j0 := eq38311 X0 X2 X3
       grind)
    | (have r₁ := eq38311 x (k X0 X0) X2
       have r₂ := eq95397 X0 x
       grind)
    | exact resolve eq38311 eq95397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38311
  have eq96384 : ∀ X0 X1 : G, (k X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15298 X1 (τ (M.op X1 X1))
       have i₂ := eq95397 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq95397 eq15298
    | exact resolve eq15298 eq95397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15298 eq95397
  have eq110561 : ∀ X0 : G, (k X0 X0) = (τ (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq96384 X0 (σ x)
       have i₂ := eq16319
       grind)
    | exact superpose eq16319 eq96384
    | exact resolve eq96384 eq16319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16319
  have eq110597 : ∀ X0 : G, y = (k X0 X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq110561 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq110561
    | exact resolve eq110561 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110561
  have eq110627 : y = (M.op x x) := by
    first
    | (have j1 := eq96269 x y x
       grind)
    | (have r₁ := eq110597 x
       have r₂ := eq96269 x y x
       grind)
    | exact resolve eq110597 eq96269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96269 eq110597
  have eq110642 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq279 X0 x
       have i₂ := eq110627
       grind)
    | exact superpose eq110627 eq279
    | exact resolve eq279 eq110627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq110695 : ∀ X0 : G, (σ (k X0 X0)) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq96228 X0 x
       have i₂ := eq110627
       grind)
    | exact superpose eq110627 eq96228
    | exact resolve eq96228 eq110627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96228
  have eq110697 : ∀ X0 : G, (k X0 X0) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq96384 X0 x
       have i₂ := eq110627
       grind)
    | exact superpose eq110627 eq96384
    | exact resolve eq96384 eq110627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96384 eq110627
  have eq110828 : (τ y) = (σ (τ y)) := by
    first
    | (have i₁ := eq110695 x
       have i₂ := eq110697 x
       grind)
    | exact superpose eq110697 eq110695
    | exact resolve eq110695 eq110697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110695 eq110697
  have eq110880 : y = (τ y) := by
    first
    | (have i₁ := eq110828
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq110828
    | exact resolve eq110828 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110828
  have eq111068 : y = (σ y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq110880
       grind)
    | exact superpose eq110880 eq10
    | exact resolve eq10 eq110880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110880
  have eq111159 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq111068
       grind)
    | exact superpose eq111068 eq14
    | exact resolve eq14 eq111068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111068
  have eq111193 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq111159
       have i₂ := eq110642 (σ x)
       grind)
    | exact superpose eq110642 eq111159
    | exact resolve eq111159 eq110642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111159
  have eq111205 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq111193
       have i₂ := eq110642 x
       grind)
    | exact superpose eq110642 eq111193
    | exact resolve eq111193 eq110642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110642 eq111193
  have eq111206 : False := by grind
  exact eq111206

/-- `Equation543`: `x = y ◇ (z ◇ (x ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxy_pyx_Equation543 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law543 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law543.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X0 (M.op X1 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq20 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k (τ X0) X1) X2
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq13
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 (M.op X0 (M.op X1 X2))) (M.op X3 X0))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X1 (M.op X2 (M.op X0 (M.op X1 X2)))
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 (M.op X2 X1)) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 X1 (M.op X0 (M.op X2 X1))
       have i₂ := eq8 X0 X2 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21
    | exact resolve eq21 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq43 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X2 X0))) = X2 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 X1 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X1 X2)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq46 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 (M.op X2 X1))) (M.op (M.op X3 X0) X3)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X3 (M.op X1 (M.op X0 (M.op X2 X1))) X2
       have i₂ := eq8 X0 X2 X1
       grind)
    | exact superpose eq8 eq23
    | exact resolve eq23 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X0 X2)) X1) (M.op (M.op X3 X0) X3)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X3 (M.op (M.op X1 (M.op X0 X2)) X1) X2
       have i₂ := eq23 X1 X2 X0
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 X1))) = X2 ∨ (M.op X0 (M.op X2 X1)) = (k (M.op X2 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 (M.op X2 X1) X1 X2
       have i₂ := eq12 (M.op X2 X1) X0
       grind)
    | (have i₁ := eq23 X0 X1 X2
       have i₂ := eq12 X0 (M.op X0 (M.op X2 X1))
       grind)
    | exact superpose eq12 eq23
    | (have j1 := eq12 (M.op X2 X1) X0
       grind)
    | exact resolve eq23 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X1 (M.op X0 X2)) X1
       have i₂ := eq23 X1 X2 X0
       grind)
    | exact superpose eq23 eq8
    | exact resolve eq8 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X2) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (M.op X1 X2) (M.op X0 X2)) X1 X2
       have i₂ := eq23 (M.op X1 X2) X2 X0
       grind)
    | exact superpose eq23 eq8
    | exact resolve eq8 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq121 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 X2) (M.op (M.op X3 X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X3 (M.op X1 X2) (M.op X1 (M.op X2 X0))
       have i₂ := eq69 X2 X1 X0
       grind)
    | exact superpose eq69 eq23
    | exact resolve eq23 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 (M.op X3 (M.op X2 (M.op X1 (M.op X1 X2)))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 (M.op X2 (M.op X1 (M.op X1 X2))) X0 X1 X3
       have i₂ := eq22 X1 X1 X2 X0
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 x X0 X1 X1
       have i₂ := eq69 x X1 (M.op X0 X1)
       grind)
    | exact superpose eq69 eq22
    | exact resolve eq22 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X3 (M.op X0 (M.op X2 (M.op X3 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 X3 X1 X2 (M.op X3 (M.op X0 (M.op X2 (M.op X3 (M.op X1 X2)))))
       have i₂ := eq23 X3 (M.op X2 (M.op X3 (M.op X1 X2))) X0
       grind)
    | exact superpose eq23 eq22
    | exact resolve eq22 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op X4 (M.op X3 (M.op (M.op X2 (M.op (M.op X0 X3) (M.op X1 X2))) X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq22 (M.op X0 X3) X1 X2 (M.op X4 (M.op X3 (M.op (M.op X2 (M.op (M.op X0 X3) (M.op X1 X2))) X4)))
       have i₂ := eq22 X3 (M.op X2 (M.op (M.op X0 X3) (M.op X1 X2))) X4 X0
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X1 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X2 (M.op X1 (M.op X1 X2))) X0 X1
       have i₂ := eq22 X1 X1 X2 X0
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : ∀ X1 X2 X3 : G, (M.op X3 (M.op X2 (M.op X1 (M.op X1 X2)))) = X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq133 x X1 X2 X3
       have i₂ := eq140 x (M.op X3 (M.op X2 (M.op X1 (M.op X1 X2))))
       grind)
    | exact superpose eq140 eq133
    | exact resolve eq133 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq157 : ∀ X2 X3 : G, (M.op X3 (M.op X2 X2)) = X3 := by
    intro X2 X3
    first
    | (have i₁ := eq156 x X2 X3
       have i₂ := eq140 x X2
       grind)
    | exact superpose eq140 eq156
    | exact resolve eq156 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq170 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 X0 X1 (M.op X2 X2)
       have i₂ := eq157 X2 X0
       grind)
    | exact superpose eq157 eq69
    | exact resolve eq69 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X1 X2 : G, (M.op X1 X1) = (M.op X2 X2) := by
    intro X1 X2
    first
    | (have i₁ := eq170 x X2 X1
       have i₂ := eq70 X2 X2 x
       grind)
    | exact superpose eq70 eq170
    | exact resolve eq170 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq195 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op X3 (M.op X1 X2))) ∨ (M.op (M.op X0 X3) X1) = (k X1 (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq43 (M.op X0 X3) X1 (M.op X2 (M.op X3 (M.op X1 X2)))
       have i₂ := eq22 X3 X1 X2 X0
       grind)
    | exact superpose eq22 eq43
    | (have j0 := eq43 (M.op X0 X3) X1 X2
       grind)
    | exact resolve eq43 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq226 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq140 X1 (M.op (M.op X2 (M.op X0 X1)) X2)
       have i₂ := eq23 X2 X1 X0
       grind)
    | exact superpose eq23 eq140
    | exact resolve eq140 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq249 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 X2))) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X0 X1 X2 (M.op X2 (M.op X0 (M.op X1 X2)))
       have i₂ := eq140 (M.op X2 (M.op X0 (M.op X1 X2))) X0
       grind)
    | exact superpose eq140 eq22
    | exact resolve eq22 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq323 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq324 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq323 X0 X1
       have i₂ := eq157 X0 X1
       grind)
    | (have i₁ := eq323 X0 X1
       have i₂ := eq157 x (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq157 eq323
    | exact resolve eq323 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq373 : ∀ X0 X1 X2 : G, (M.op (σ X1) (M.op (σ X0) (M.op X2 (σ (k X0 X1))))) = X2 ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (σ X1) (σ X0)
       have i₂ := eq46 X1 X0
       grind)
    | exact superpose eq46 eq8
    | (have j1 := eq46 X1 X0
       grind)
    | exact resolve eq8 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq404 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (M.op (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq157 (σ X2) X1
       have i₂ := eq46 X0 X2
       grind)
    | exact superpose eq46 eq157
    | (have j1 := eq46 X0 X2
       grind)
    | exact resolve eq157 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq435 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq324 X2 X1
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq324 X0 X1
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq324
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq324 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq444 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (M.op X1 X1)
       have i₂ := eq324 X1 (σ X0)
       grind)
    | exact superpose eq324 eq29
    | exact resolve eq29 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq445 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X1 X1)
       have i₂ := eq324 X1 (τ X0)
       grind)
    | exact superpose eq324 eq16
    | exact resolve eq16 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq452 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq445 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq445
    | exact resolve eq445 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq453 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq444 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq444
    | exact resolve eq444 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq521 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq70 X3 (M.op X0 X2) (M.op X1 X2)
       have i₂ := eq70 X1 X0 X2
       grind)
    | exact superpose eq70 eq70
    | exact resolve eq70 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq533 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op X3 X0))) = (M.op (M.op X1 (M.op X2 X3)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq70 (M.op X2 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq69 X3 X2 X0
       grind)
    | exact superpose eq69 eq70
    | exact resolve eq70 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq960 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq102 X1 X1
       have i₂ := eq181 X1 x
       grind)
    | (have i₁ := eq102 x x
       have i₂ := eq181 X1 x
       grind)
    | exact superpose eq181 eq102
    | (have j0 := eq102 X0 X0
       grind)
    | (have r₁ := eq102 x x
       have r₂ := eq181 x x
       grind)
    | (have r₁ := eq102 X1 X1
       have r₂ := eq181 X1 X1
       grind)
    | exact resolve eq102 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq966 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq102 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq969 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq960 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq1011 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq966 (τ X0)
       grind)
    | exact superpose eq966 eq33
    | exact resolve eq33 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1014 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1011 X0
       have i₂ := eq966 X0
       grind)
    | exact superpose eq966 eq1011
    | exact resolve eq1011 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq1149 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq452 (σ (M.op X1 X1)) X1
       have i₂ := eq969 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq969 eq452
    | exact resolve eq452 eq969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq1152 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq453 (τ (M.op X1 X1)) X1
       have i₂ := eq969 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq969 eq453
    | exact resolve eq453 eq969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1158 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq969 X0 (τ X1)
       grind)
    | exact superpose eq969 eq16
    | exact resolve eq16 eq969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969
  have eq1165 : ∀ X0 X1 : G, (k X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1158 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1158
    | exact resolve eq1158 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158
  have eq1477 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 X1) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1165 X2 X1
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq1165 X0 X1
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq1165
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq1165 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1500 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq453 (τ (M.op X1 X1)) X1
       have i₂ := eq1165 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq1165 eq453
    | exact resolve eq453 eq1165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453 eq1165
  have eq1547 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 X1) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1477 X0 X1 X2
       have i₂ := eq966 X1
       grind)
    | exact superpose eq966 eq1477
    | (have j0 := eq1477 X0 X1 X2
       grind)
    | exact resolve eq1477 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966 eq1477
  have eq1912 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq157 x X1
       have i₂ := eq1149 x X0
       grind)
    | exact superpose eq1149 eq157
    | exact resolve eq157 eq1149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2267 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 X0)) (M.op (M.op X1 X2) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 X1 (M.op X1 X2) X2
       have i₂ := eq1152 (M.op X1 X2) X0
       grind)
    | exact superpose eq1152 eq69
    | exact resolve eq69 eq1152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2274 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq157 x X1
       have i₂ := eq1152 x X0
       grind)
    | exact superpose eq1152 eq157
    | exact resolve eq157 eq1152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq2355 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X3) X4) = (M.op (M.op (M.op X1 X0) X1) (M.op (M.op X5 (M.op (M.op X2 (M.op X3 X0)) X2)) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq65 (M.op (M.op X2 (M.op X3 X0)) X2) X1 (M.op (M.op X4 X3) X4) X5
       have i₂ := eq65 X3 X2 X0 X4
       grind)
    | exact superpose eq65 eq65
    | exact resolve eq65 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2389 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 (M.op X3 X4)) X2) (M.op (M.op X0 (M.op X1 (M.op X1 X0))) X3)) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq65 X3 X2 X4 X3
       have i₂ := eq143 X3 X1 X0
       grind)
    | exact superpose eq143 eq65
    | exact resolve eq65 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2433 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 (M.op X2 X0)) X1) X3) = (M.op X0 (M.op X3 (M.op (M.op X4 X2) X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq70 X3 (M.op (M.op X1 (M.op X2 X0)) X1) (M.op (M.op X4 X2) X4)
       have i₂ := eq65 X2 X1 X0 X4
       grind)
    | exact superpose eq65 eq70
    | exact resolve eq70 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2439 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) X3) = (M.op (M.op (M.op X1 (M.op X2 X0)) X1) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq140 (M.op (M.op X1 (M.op X2 X0)) X1) (M.op (M.op X3 X2) X3)
       have i₂ := eq65 X2 X1 X0 X3
       grind)
    | exact superpose eq65 eq140
    | exact resolve eq140 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2442 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X3 X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq2439 X3 x X2 X0
       have i₂ := eq226 X2 X3 x
       grind)
    | exact superpose eq226 eq2439
    | exact resolve eq2439 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2439
  have eq2448 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X0 X2) X3) = (M.op X0 (M.op X3 (M.op (M.op X4 X2) X4))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq2433 X0 x X2 X3 X4
       have i₂ := eq226 X2 X0 x
       grind)
    | exact superpose eq226 eq2433
    | exact resolve eq2433 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2433
  have eq2481 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 (M.op X3 X4)) X2) (M.op X0 (M.op X1 (M.op (M.op X1 X0) X3)))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2389 X0 X1 X2 X3 X4
       have i₂ := eq533 X3 X0 X1 (M.op X1 X0)
       grind)
    | exact superpose eq533 eq2389
    | exact resolve eq2389 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2389
  have eq2508 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) X4) = (M.op (M.op X1 X0) (M.op X1 (M.op (M.op X2 (M.op X3 X0)) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2355 X0 X1 X2 X3 X4 x
       have i₂ := eq121 (M.op (M.op X2 (M.op X3 X0)) X2) (M.op X1 X0) X1 x
       grind)
    | exact superpose eq121 eq2355
    | exact resolve eq2355 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq2355
  have eq2560 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X4 X3) (M.op X0 (M.op X1 (M.op (M.op X1 X0) X3)))) = X4 := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq2481 X0 X1 x X3 X4
       have i₂ := eq226 X3 X4 x
       grind)
    | exact superpose eq226 eq2481
    | exact resolve eq2481 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2481
  have eq2577 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X4 X3) X4) = (M.op (M.op (M.op X1 X0) (M.op X3 X0)) X1) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq2508 X0 X1 x X3 X4
       have i₂ := eq2448 (M.op X1 X0) (M.op X3 X0) X1 x
       grind)
    | exact superpose eq2448 eq2508
    | exact resolve eq2508 eq2448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2448 eq2508
  have eq2607 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X4 X3) X4) = (M.op (M.op X1 X0) (M.op X3 (M.op X0 X1))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq2577 X0 X1 X3 X4
       have i₂ := eq533 X1 (M.op X1 X0) X3 X0
       grind)
    | exact superpose eq533 eq2577
    | exact resolve eq2577 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2577
  have eq2618 : ∀ X1 X3 X4 : G, (M.op (M.op X4 X3) X4) = (M.op (M.op X1 X1) X3) := by
    intro X1 X3 X4
    first
    | (have i₁ := eq2607 x X1 X3 X4
       have i₂ := eq521 X1 x X1 X3
       grind)
    | exact superpose eq521 eq2607
    | exact resolve eq2607 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521 eq2607
  have eq2622 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1912 X2 X1
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq1912 X0 X1
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq1912
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq1912 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3043 : ∀ X0 X1 : G, (M.op X1 (τ (τ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2274 (τ (M.op X0 X0)) X1
       have i₂ := eq2274 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq2274 eq2274
    | exact resolve eq2274 eq2274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3164 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X0)) X3) = (M.op X4 (M.op X3 (M.op (M.op X1 X2) (M.op X4 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq141 X3 (M.op X1 (M.op X2 X0)) (M.op X1 X2) X4
       have i₂ := eq69 X2 X1 X0
       grind)
    | exact superpose eq69 eq141
    | exact resolve eq141 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3189 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op X4 (M.op X2 (M.op X0 X4))) (M.op X3 (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq141 X3 (M.op X1 X2) X1 (M.op X4 (M.op X2 (M.op X0 X4)))
       have i₂ := eq64 X2 X4 X0 X1
       grind)
    | exact superpose eq64 eq141
    | exact resolve eq141 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3190 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op (M.op X4 (M.op X2 X0)) X4) (M.op X3 (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq141 X3 (M.op X1 X2) X1 (M.op (M.op X4 (M.op X2 X0)) X4)
       have i₂ := eq65 X2 X4 X0 X1
       grind)
    | exact superpose eq65 eq141
    | exact resolve eq141 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq3214 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X1)) = (M.op X2 (M.op X0 (M.op X3 (M.op X2 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq141 (M.op X0 (M.op X3 (M.op X2 X1))) X2 X1 X3
       have i₂ := eq70 X1 X0 (M.op X3 (M.op X2 X1))
       grind)
    | exact superpose eq70 eq141
    | exact resolve eq141 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3256 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X1)) = (M.op X1 (M.op X3 (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq140 X2 (M.op X1 (M.op X3 (M.op X2 (M.op X0 X3))))
       have i₂ := eq141 X1 X0 X3 X2
       grind)
    | exact superpose eq141 eq140
    | exact resolve eq140 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq3263 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X1 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3256 X0 X1 X2 x
       have i₂ := eq249 X2 X0 x
       grind)
    | exact superpose eq249 eq3256
    | exact resolve eq3256 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3256
  have eq3311 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op X0 X2) (M.op X3 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3190 X0 X1 X2 X3 x
       have i₂ := eq226 X2 X0 x
       grind)
    | exact superpose eq226 eq3190
    | exact resolve eq3190 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq3190
  have eq3312 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) X3) = (M.op X4 (M.op X2 (M.op (M.op X0 X4) (M.op X3 (M.op X1 X0))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3189 X0 X1 X2 X3 X4
       have i₂ := eq533 (M.op X3 (M.op X1 X0)) X4 X2 (M.op X0 X4)
       grind)
    | exact superpose eq533 eq3189
    | exact resolve eq3189 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3189
  have eq3332 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3164 X0 X1 X2 X3 x
       have i₂ := eq3214 X3 X0 x (M.op X1 X2)
       grind)
    | exact superpose eq3214 eq3164
    | exact resolve eq3164 eq3214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3164 eq3214
  have eq3380 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X1 X2) X3) = (M.op X4 (M.op X2 (M.op (M.op X1 X4) X3))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq3312 x X1 X2 X3 X4
       have i₂ := eq3311 x X1 X4 X3
       grind)
    | exact superpose eq3311 eq3312
    | exact resolve eq3312 eq3311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3311 eq3312
  have eq3392 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op X3 X0)) = (M.op X1 (M.op X2 (M.op X0 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3332 X0 X1 X2 X3
       have i₂ := eq533 X3 X1 X2 X0
       grind)
    | exact superpose eq533 eq3332
    | exact resolve eq3332 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533 eq3332
  have eq3801 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq49 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq49
    | exact resolve eq49 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3844 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq10
    | (have j1 := eq49 X1 X0
       grind)
    | exact resolve eq10 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq3994 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3801 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq3801
    | (have j0 := eq3801 X0 X1
       grind)
    | exact resolve eq3801 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3801
  have eq11893 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) X3) = (M.op X4 (M.op (M.op X2 (M.op X0 X3)) (M.op (M.op X1 X0) X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq142 X3 (M.op X1 X2) X1 (M.op X2 (M.op X0 X3)) X4
       have i₂ := eq64 X2 X3 X0 X1
       grind)
    | exact superpose eq64 eq142
    | exact resolve eq142 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq142
  have eq12168 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op X1 X0) (M.op X2 (M.op X0 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11893 X0 X1 X2 X3 x
       have i₂ := eq249 (M.op X2 (M.op X0 X3)) (M.op X1 X0) x
       grind)
    | exact superpose eq249 eq11893
    | exact resolve eq11893 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11893
  have eq12367 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op X1 (M.op X0 (M.op (M.op X0 X3) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12168 X0 X1 X2 X3
       have i₂ := eq3392 (M.op X0 X3) X1 X0 X2
       grind)
    | exact superpose eq3392 eq12168
    | exact resolve eq12168 eq3392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12168
  have eq15673 : ∀ X0 X1 X2 : G, (k (M.op X2 X1) (M.op X2 (M.op X1 X0))) = X0 ∨ (M.op X1 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 (M.op X1 (M.op X0 X2)) X0 X1
       have i₂ := eq69 X0 X1 X2
       grind)
    | exact superpose eq69 eq68
    | exact resolve eq68 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq69
  have eq23270 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) = (M.op (M.op X3 (M.op X0 X4)) (M.op X4 (M.op X0 X1))) ∨ (M.op (M.op X1 X3) X0) = (k X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq143 X2 X4 (M.op X3 (M.op X0 X4))
       have i₂ := eq195 X1 X0 X4 X3
       grind)
    | (have i₁ := eq143 X0 X1 X0
       have i₂ := eq195 X0 X1 X2 X3
       grind)
    | exact superpose eq195 eq143
    | (have j1 := eq195 X1 X0 X2 X3
       grind)
    | exact resolve eq143 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq23335 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) = (M.op X3 (M.op (M.op X0 X4) (M.op (M.op X0 X1) X4))) ∨ (M.op (M.op X1 X3) X0) = (k X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq23270 X0 X1 X2 X3 X4
       have i₂ := eq3392 (M.op X0 X1) X3 (M.op X0 X4) X4
       grind)
    | exact superpose eq3392 eq23270
    | (have j0 := eq23270 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq23270 eq3392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23270
  have eq23805 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) = (M.op X3 (M.op X4 (M.op (M.op X0 X1) (M.op X0 X4)))) ∨ (M.op (M.op X1 X3) X0) = (k X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq23335 X0 X1 X2 X3 X4
       have i₂ := eq3263 (M.op X0 X1) X4 (M.op X0 X4)
       grind)
    | (have i₁ := eq23335 X0 X1 X2 X3 X4
       have i₂ := eq3263 (M.op X0 X1) (M.op X0 X4) X4
       grind)
    | exact superpose eq3263 eq23335
    | (have j0 := eq23335 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq23335 eq3263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23335
  have eq24109 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) = (M.op X3 (M.op X0 (M.op X0 X1))) ∨ (M.op (M.op X1 X3) X0) = (k X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23805 X0 X1 X2 X3 x
       have i₂ := eq249 (M.op X0 X1) X0 x
       grind)
    | exact superpose eq249 eq23805
    | (have j0 := eq23805 X0 X1 X2 X3 x
       grind)
    | exact resolve eq23805 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq23805
  have eq24321 : ∀ X0 X1 X2 X3 : G, (M.op X3 X1) = (M.op X2 X2) ∨ (M.op (M.op X1 X3) X0) = (k X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24109 X0 X1 X2 X3
       have i₂ := eq140 X0 X1
       grind)
    | exact superpose eq140 eq24109
    | (have j0 := eq24109 X0 X1 X2 X3
       grind)
    | exact resolve eq24109 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24109
  have eq24917 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = (M.op (τ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2618 (τ X0) X2 X1
       have i₂ := eq1014 X0
       grind)
    | exact superpose eq1014 eq2618
    | exact resolve eq2618 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq25004 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X3) = (M.op (M.op (M.op X0 X0) X1) (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq70 X3 (M.op X2 X1) X2
       have i₂ := eq2618 X0 X1 X2
       grind)
    | (have i₁ := eq70 X0 (M.op X1 X1) X3
       have i₂ := eq2618 X1 X3 x
       grind)
    | exact superpose eq2618 eq70
    | exact resolve eq70 eq2618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq25062 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (τ (M.op X2 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2274 X2 (M.op (τ (M.op X2 X2)) X1)
       have i₂ := eq2618 X0 X1 (τ (M.op X2 X2))
       grind)
    | (have i₁ := eq2274 X0 (M.op X1 X1)
       have i₂ := eq2618 X1 (τ (M.op X0 X0)) x
       grind)
    | exact superpose eq2618 eq2274
    | exact resolve eq2274 eq2618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25460 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X3) = (M.op (M.op X0 X0) (M.op X1 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25004 X0 X1 X2 X3
       have i₂ := eq3392 X2 (M.op X0 X0) X1 X3
       grind)
    | exact superpose eq3392 eq25004
    | exact resolve eq25004 eq3392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25004
  have eq25713 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X3) = (M.op X0 (M.op X0 (M.op (M.op X2 X3) X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25460 X0 X1 X2 X3
       have i₂ := eq3392 (M.op X2 X3) X0 X0 X1
       grind)
    | exact superpose eq3392 eq25460
    | exact resolve eq25460 eq3392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3392 eq25460
  have eq25884 : ∀ X1 X2 X3 : G, (M.op (M.op X2 X3) X1) = (M.op (M.op X2 X1) X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq25713 x X3 X2 X1
       have i₂ := eq140 x (M.op (M.op X2 X1) X3)
       grind)
    | exact superpose eq140 eq25713
    | exact resolve eq25713 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25713
  have eq31047 : ∀ X0 X1 X2 : G, (M.op (σ X1) (M.op X0 (M.op X2 (σ (k (τ X0) X1))))) = X2 ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq373 (τ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq373
    | exact resolve eq373 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq31358 : ∀ X0 X1 X2 : G, (M.op (σ X1) (M.op X0 (M.op X2 (k X0 (σ X1))))) = X2 ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31047 X0 X1 X2
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq31047
    | (have j0 := eq31047 X0 X1 X2
       grind)
    | exact resolve eq31047 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq31047
  have eq99780 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1912 X2 X1
       have i₂ := eq3994 X0 X2
       grind)
    | (have i₁ := eq1912 X0 X1
       have i₂ := eq3994 (M.op X0 X0) X1
       grind)
    | exact superpose eq3994 eq1912
    | (have j1 := eq3994 X0 X2
       grind)
    | exact resolve eq1912 eq3994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3994
  have eq102036 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq435 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq289903 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X1 ∨ (M.op (τ X1) X2) = (k X2 (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X1
       have i₂ := eq1547 (τ X1) X0 X2
       grind)
    | exact superpose eq1547 eq10
    | (have j1 := eq1547 (τ X1) X1 X2
       grind)
    | exact resolve eq10 eq1547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300166 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq404 x X0 y
       grind)
    | exact superpose eq404 eq14
    | (have j1 := eq404 x X0 x
       grind)
    | exact resolve eq14 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq300801 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq300166 X0
       have j1 := eq99780 x X0 x
       grind)
    | (have r₁ := eq300166 X0
       have r₂ := eq99780 x x y
       grind)
    | exact resolve eq300166 eq99780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99780 eq300166
  have eq301710 : ∀ X0 : G, (M.op X0 X0) = (σ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1149 X0 (σ x)
       have i₂ := eq300801 (σ x)
       grind)
    | exact superpose eq300801 eq1149
    | exact resolve eq1149 eq300801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149
  have eq301712 : ∀ X0 : G, (σ x) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1152 (σ x) X0
       have i₂ := eq300801 (σ x)
       grind)
    | exact superpose eq300801 eq1152
    | exact resolve eq1152 eq300801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301713 : ∀ X0 : G, (M.op X0 X0) = (τ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1152 X0 (σ x)
       have i₂ := eq300801 (σ x)
       grind)
    | exact superpose eq300801 eq1152
    | exact resolve eq1152 eq300801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152
  have eq301746 : ∀ X0 : G, (M.op X0 (τ (σ x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2274 (σ x) X0
       have i₂ := eq300801 (σ x)
       grind)
    | exact superpose eq300801 eq2274
    | exact resolve eq2274 eq300801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301750 : ∀ X0 : G, (M.op X0 (τ (τ (σ x)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq3043 (σ x) X0
       have i₂ := eq300801 (σ x)
       grind)
    | exact superpose eq300801 eq3043
    | exact resolve eq3043 eq300801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3043
  have eq301802 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (τ (σ x)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24917 (σ x) X0 X1
       have i₂ := eq300801 (σ x)
       grind)
    | exact superpose eq300801 eq24917
    | exact resolve eq24917 eq300801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24917
  have eq301806 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (τ (σ x)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25062 X0 X1 (σ x)
       have i₂ := eq300801 (σ x)
       grind)
    | exact superpose eq300801 eq25062
    | exact resolve eq25062 eq300801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25062
  have eq301880 : ∀ X0 : G, (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq140 X0 (σ x)
       have i₂ := eq300801 X0
       grind)
    | exact superpose eq300801 eq140
    | exact resolve eq140 eq300801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302007 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (M.op (σ x) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2442 X1 X0 (σ x)
       have i₂ := eq300801 (M.op (σ x) X0)
       grind)
    | exact superpose eq300801 eq2442
    | exact resolve eq2442 eq300801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2442
  have eq302010 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op (σ x) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2618 X1 X0 (σ x)
       have i₂ := eq300801 (M.op (σ x) X0)
       grind)
    | exact superpose eq300801 eq2618
    | exact resolve eq2618 eq300801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2618 eq300801
  have eq302281 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq301806 X0 X1
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq301806
    | exact resolve eq301806 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301806
  have eq302283 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq301802 X0 X1
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq301802
    | exact resolve eq301802 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301802
  have eq302321 : ∀ X0 : G, (M.op X0 (τ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq301750 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq301750
    | exact resolve eq301750 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301750
  have eq302323 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq301746 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq301746
    | exact resolve eq301746 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301746
  have eq302348 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq301713 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq301713
    | exact resolve eq301713 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301713
  have eq302349 : (σ x) = (τ (σ x)) := by
    first
    | (have i₁ := eq301712 x
       have i₂ := eq301880 x
       grind)
    | exact superpose eq301880 eq301712
    | exact resolve eq301712 eq301880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301712
  have eq302351 : (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq301710 x
       have i₂ := eq301880 x
       grind)
    | exact superpose eq301880 eq301710
    | exact resolve eq301710 eq301880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301710
  have eq302486 : ∀ X1 : G, (M.op (σ x) X1) = (M.op x X1) := by
    intro X1
    first
    | (have i₁ := eq302281 x X1
       have i₂ := eq301880 x
       grind)
    | exact superpose eq301880 eq302281
    | exact resolve eq302281 eq301880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302281
  have eq302529 : x = (σ x) := by
    first
    | (have i₁ := eq302349
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq302349
    | exact resolve eq302349 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302349
  have eq306510 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq302529
       grind)
    | exact superpose eq302529 eq14
    | exact resolve eq14 eq302529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317727 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (M.op X2 (M.op x X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12367 X2 X0 X1 X2
       have i₂ := eq302348 X2
       grind)
    | exact superpose eq302348 eq12367
    | exact resolve eq12367 eq302348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12367 eq302348
  have eq331417 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (τ X1) X0)
       have i₂ := eq3844 X0 X1
       grind)
    | exact superpose eq3844 eq9
    | (have j1 := eq3844 X0 X1
       grind)
    | exact resolve eq9 eq3844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3844
  have eq331623 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq331417 X0 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq331417
    | (have j0 := eq331417 X0 X1
       grind)
    | exact resolve eq331417 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331417
  have eq332039 : ∀ X0 X1 : G, (σ (σ x)) = X1 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq331623 X0 X1
       have i₂ := eq301880 X0
       grind)
    | exact superpose eq301880 eq331623
    | (have j0 := eq331623 X0 X1
       grind)
    | exact resolve eq331623 eq301880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331623
  have eq332329 : ∀ X0 X1 : G, (σ x) = X1 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq332039 X0 X1
       have i₂ := eq302351
       grind)
    | exact superpose eq302351 eq332039
    | (have j0 := eq332039 X0 X1
       grind)
    | exact resolve eq332039 eq302351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332039
  have eq332486 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ x = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq332329 X0 X1
       have i₂ := eq302529
       grind)
    | exact superpose eq302529 eq332329
    | (have j0 := eq332329 X0 X1
       grind)
    | exact resolve eq332329 eq302529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332329
  have eq366472 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) X3) = (k (M.op X1 (τ (M.op X2 X2))) (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq15673 (M.op (M.op X1 X2) X1) (τ (M.op X0 X0)) X2
       have i₂ := eq2267 X0 X1 X2
       grind)
    | exact superpose eq2267 eq15673
    | (have j0 := eq15673 X3 (M.op X3 X0) (k (M.op X1 (τ (M.op X2 X2))) (M.op X1 X0))
       grind)
    | exact resolve eq15673 eq2267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2267 eq15673
  have eq366516 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X0) X3) = (k X1 (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq366472 X0 X1 x X3
       have i₂ := eq2274 x X1
       grind)
    | exact superpose eq2274 eq366472
    | (have j0 := eq366472 (M.op (M.op X3 X0) X3) (k X1 (M.op X1 X0)) x X3
       grind)
    | exact resolve eq366472 eq2274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2274 eq366472
  have eq366577 : ∀ X0 X1 : G, (M.op (σ x) X0) = (k X1 (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq366516 X0 X1 x
       have i₂ := eq302007 X0 x
       grind)
    | exact superpose eq302007 eq366516
    | (have j0 := eq366516 (M.op (σ x) X0) (k X1 (M.op X1 X0)) x
       grind)
    | exact resolve eq366516 eq302007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366516
  have eq366598 : ∀ X0 X1 : G, (k X1 (M.op X1 X0)) = (M.op x X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq366577 X0 X1
       have i₂ := eq302486 X0
       grind)
    | exact superpose eq302486 eq366577
    | (have j0 := eq366577 (k X1 (M.op X1 X0)) (M.op x X0)
       grind)
    | exact resolve eq366577 eq302486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366577
  have eq380836 : ∀ X0 X1 X2 : G, (M.op (σ X0) X1) = (M.op x X1) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq302283 X1 X1
       have i₂ := eq1547 X0 X1 X2
       grind)
    | exact superpose eq1547 eq302283
    | (have j1 := eq1547 X0 X1 X2
       grind)
    | exact resolve eq302283 eq1547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1547
  have eq381372 : ∀ X0 X1 : G, (M.op x X0) ≠ X1 ∨ (k X1 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq102036 X1 (M.op X1 X0)
       have i₂ := eq302283 X1 X0
       grind)
    | exact superpose eq302283 eq102036
    | (have j0 := eq102036 X1 (M.op X1 X0)
       grind)
    | (have r₁ := eq102036 (M.op x X1) (M.op (M.op x X1) X1)
       have r₂ := eq302283 (M.op x X1) X1
       grind)
    | exact resolve eq102036 eq302283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102036
  have eq411084 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op x (σ y)) ∨ (M.op (M.op y x) X1) = (k X1 (M.op y x)) := by
    intro X0 X1
    first
    | (have i₁ := eq306510
       have i₂ := eq24321 X1 y X0 x
       grind)
    | exact superpose eq24321 eq306510
    | (have j1 := eq24321 X1 y x x
       grind)
    | exact resolve eq306510 eq24321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24321
  have eq411273 : ∀ X1 : G, (σ (σ x)) ≠ (M.op x (σ y)) ∨ (M.op (M.op y x) X1) = (k X1 (M.op y x)) := by
    intro X1
    first
    | (have i₁ := eq411084 x X1
       have i₂ := eq301880 x
       grind)
    | exact superpose eq301880 eq411084
    | (have j0 := eq411084 x X1
       grind)
    | exact resolve eq411084 eq301880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411084
  have eq411398 : ∀ X1 : G, (σ x) ≠ (M.op x (σ y)) ∨ (M.op (M.op y x) X1) = (k X1 (M.op y x)) := by
    intro X1
    first
    | (have i₁ := eq411273 X1
       have i₂ := eq302351
       grind)
    | exact superpose eq302351 eq411273
    | (have j0 := eq411273 X1
       grind)
    | exact resolve eq411273 eq302351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302351 eq411273
  have eq411485 : ∀ X1 : G, x ≠ (M.op x (σ y)) ∨ (M.op (M.op y x) X1) = (k X1 (M.op y x)) := by
    intro X1
    first
    | (have i₁ := eq411398 X1
       have i₂ := eq302529
       grind)
    | exact superpose eq302529 eq411398
    | (have j0 := eq411398 X1
       grind)
    | exact resolve eq411398 eq302529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411398
  have eq411542 : ∀ X1 : G, (k X1 y) = (M.op y X1) ∨ x ≠ (M.op x (σ y)) := by
    intro X1
    first
    | (have i₁ := eq411485 X1
       have i₂ := eq302323 y
       grind)
    | exact superpose eq302323 eq411485
    | exact resolve eq411485 eq302323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411485
  have eq411577 : ∀ X1 : G, (k X1 y) = (M.op y X1) := by
    intro X1
    first
    | (have j0 := eq411542 X1
       have j1 := eq2622 y X1 X1
       grind)
    | (have r₁ := eq411542 X1
       have r₂ := eq2622 y x x
       grind)
    | exact resolve eq411542 eq2622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2622 eq411542
  have eq452560 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 (M.op X1 (M.op x X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq381372 (M.op x X0) X1
       have i₂ := eq140 x X0
       grind)
    | exact superpose eq140 eq381372
    | (have j0 := eq381372 (M.op x X0) X1
       grind)
    | (have r₁ := eq381372 (M.op x X1) X1
       have r₂ := eq140 x X1
       grind)
    | (have r₁ := eq381372 X0 (M.op X0 (M.op X0 (M.op x X0)))
       have r₂ := eq140 X0 (M.op x X0)
       grind)
    | exact resolve eq381372 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381372
  have eq456811 : ∀ X0 : G, (k X0 (M.op X0 (M.op x X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq452560 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452560
  have eq457290 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (M.op x (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (M.op (σ X0) (M.op x (σ X0)))
       have i₂ := eq456811 (σ X0)
       grind)
    | exact superpose eq456811 eq29
    | exact resolve eq29 eq456811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq456811
  have eq457324 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (M.op x (σ X0))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq457290 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq457290
    | exact resolve eq457290 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457290
  have eq462527 : ∀ X0 X1 : G, (M.op (σ X1) (k X0 (σ X1))) = X0 ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31358 X0 X1 X0
       have i₂ := eq140 X0 (k X0 (σ X1))
       grind)
    | exact superpose eq140 eq31358
    | (have j0 := eq31358 X0 X1 x
       grind)
    | exact resolve eq31358 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31358
  have eq462602 : ∀ X0 X1 : G, (σ X1) = (σ x) ∨ (M.op (σ X1) (k X0 (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq462527 X0 X1
       have i₂ := eq301880 X0
       grind)
    | exact superpose eq301880 eq462527
    | (have j0 := eq462527 X0 X1
       grind)
    | exact resolve eq462527 eq301880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462527
  have eq462652 : ∀ X0 X1 : G, (M.op (σ X1) (k X0 (σ X1))) = X0 ∨ (σ X1) = x := by
    intro X0 X1
    first
    | (have i₁ := eq462602 X0 X1
       have i₂ := eq302529
       grind)
    | exact superpose eq302529 eq462602
    | (have j0 := eq462602 X0 X1
       grind)
    | exact resolve eq462602 eq302529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462602
  have eq462728 : ∀ X0 X1 : G, (M.op X0 (k X1 X0)) = X1 ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq462652 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq462652
    | exact resolve eq462652 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462652
  have eq463773 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X2 (M.op X3 (M.op (M.op X3 X2) (k X0 X1))))) = X1 ∨ x = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2560 X2 X3 (k X0 X1) X1
       have i₂ := eq462728 X1 X0
       grind)
    | exact superpose eq462728 eq2560
    | (have j1 := eq462728 X1 X1
       grind)
    | exact resolve eq2560 eq462728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2560
  have eq463909 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op X3 X3) (k X0 X1))) = X1 ∨ x = X1 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq463773 X0 X1 x X3
       have i₂ := eq3380 X3 X3 (k X0 X1) x
       grind)
    | exact superpose eq3380 eq463773
    | (have j0 := eq463773 X0 X1 x X3
       grind)
    | exact resolve eq463773 eq3380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3380 eq463773
  have eq464036 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (k X0 X1))) = X1 ∨ x = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq463909 X0 X1 x
       have i₂ := eq302010 (k X0 X1) x
       grind)
    | exact superpose eq302010 eq463909
    | (have j0 := eq463909 X0 X1 x
       grind)
    | exact resolve eq463909 eq302010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302010 eq463909
  have eq464127 : ∀ X0 X1 : G, (M.op X0 (M.op x (k X0 X1))) = X1 ∨ x = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq464036 X0 X1
       have i₂ := eq302486 (k X0 X1)
       grind)
    | exact superpose eq302486 eq464036
    | (have j0 := eq464036 X0 X1
       grind)
    | exact resolve eq464036 eq302486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464036
  have eq464881 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op x (k X2 X0)) (M.op X2 X0)) ∨ x = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq143 X1 X2 (M.op x (k X2 X0))
       have i₂ := eq464127 X2 X0
       grind)
    | exact superpose eq464127 eq143
    | (have j1 := eq464127 X0 X0
       grind)
    | exact resolve eq143 eq464127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq464127
  have eq465186 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X0 (M.op X2 (M.op x (k X2 X0)))) ∨ x = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq464881 X0 X1 X2
       have i₂ := eq3263 X2 X0 (M.op x (k X2 X0))
       grind)
    | (have i₁ := eq464881 X0 X1 X2
       have i₂ := eq3263 X2 (M.op x (k X2 X0)) X0
       grind)
    | exact superpose eq3263 eq464881
    | (have j0 := eq464881 X0 X1 X2
       grind)
    | exact resolve eq464881 eq3263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464881
  have eq465494 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 (k X2 X0)) X2) ∨ x = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq465186 X0 X1 X2
       have i₂ := eq317727 X0 (k X2 X0) X2
       grind)
    | exact superpose eq317727 eq465186
    | (have j0 := eq465186 X0 X1 X2
       grind)
    | exact resolve eq465186 eq317727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317727 eq465186
  have eq465672 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X2) (k X2 X0)) ∨ x = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq465494 X0 X1 X2
       have i₂ := eq25884 X2 X0 (k X2 X0)
       grind)
    | (have i₁ := eq465494 X0 X1 X2
       have i₂ := eq25884 (k X2 X0) X0 X2
       grind)
    | exact superpose eq25884 eq465494
    | (have j0 := eq465494 X0 X1 X2
       grind)
    | exact resolve eq465494 eq25884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25884 eq465494
  have eq465780 : ∀ X0 X2 : G, (σ x) = (M.op (M.op X0 X2) (k X2 X0)) ∨ x = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq465672 X0 x X2
       have i₂ := eq301880 x
       grind)
    | exact superpose eq301880 eq465672
    | (have j0 := eq465672 X0 x X2
       grind)
    | exact resolve eq465672 eq301880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465672
  have eq465847 : ∀ X0 X2 : G, x = (M.op (M.op X0 X2) (k X2 X0)) ∨ x = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq465780 X0 X2
       have i₂ := eq302529
       grind)
    | exact superpose eq302529 eq465780
    | (have j0 := eq465780 (M.op (M.op X0 X2) (k X2 X0)) X2
       grind)
    | exact resolve eq465780 eq302529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465780
  have eq470383 : ∀ X0 X1 : G, x = (M.op X0 (k (k X0 X1) X1)) ∨ x = X1 ∨ x = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq465847 X1 (k X0 X1)
       have i₂ := eq462728 X1 X0
       grind)
    | exact superpose eq462728 eq465847
    | (have j0 := eq465847 (M.op X0 (k (k X0 X1) X1)) x
       have j1 := eq462728 (M.op X0 (k (k X0 X1) X1)) X1
       grind)
    | exact resolve eq465847 eq462728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465847
  have eq470723 : ∀ X0 X1 : G, x = (M.op X0 (k (k X0 X1) X1)) ∨ x = X1 := by
    intro X0 X1
    first
    | (have j0 := eq470383 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470383
  have eq476256 : ∀ X0 X1 : G, (k (k X0 X1) X1) = (M.op X0 x) ∨ x = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq140 X0 (k (k X0 X1) X1)
       have i₂ := eq470723 X0 X1
       grind)
    | exact superpose eq470723 eq140
    | (have j1 := eq470723 X0 X1
       grind)
    | exact resolve eq140 eq470723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470723
  have eq476516 : ∀ X0 X1 : G, (k (k X0 X1) X1) = X0 ∨ x = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq476256 X0 X1
       have i₂ := eq302323 X0
       grind)
    | exact superpose eq302323 eq476256
    | (have j0 := eq476256 X0 X1
       grind)
    | exact resolve eq476256 eq302323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476256
  have eq477482 : ∀ X0 X1 : G, (σ (k (k (τ X0) X1) X1)) = X0 ∨ (σ X1) = x := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1 X1
       have i₂ := eq476516 X0 (σ X1)
       grind)
    | exact superpose eq476516 eq20
    | (have j1 := eq476516 X0 (σ X1)
       grind)
    | exact resolve eq20 eq476516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq476516
  have eq588896 : ∀ X0 X1 : G, (σ (k (M.op (τ X0) (τ X1)) (τ X0))) = X1 ∨ (σ (τ X0)) = x ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq477482 X1 (τ X0)
       have i₂ := eq332486 (τ X1) X0
       grind)
    | exact superpose eq332486 eq477482
    | (have j0 := eq477482 X0 (τ X0)
       have j1 := eq332486 X0 (σ (τ X0))
       grind)
    | exact resolve eq477482 eq332486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332486 eq477482
  have eq589008 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) (τ X1))) X0) = X1 ∨ (σ (τ X0)) = x ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq588896 X0 X1
       have i₂ := eq17 X0 (M.op (τ X0) (τ X1))
       grind)
    | exact superpose eq17 eq588896
    | (have j0 := eq588896 X0 X1
       grind)
    | exact resolve eq588896 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq588896
  have eq589090 : ∀ X0 X1 : G, x = X0 ∨ (k (σ (M.op (τ X0) (τ X1))) X0) = X1 ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq589008 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq589008
    | (have j0 := eq589008 X0 X1
       grind)
    | exact resolve eq589008 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589008
  have eq589091 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) (τ X1))) X0) = X1 ∨ x = X0 := by
    intro X0 X1
    first
    | (have j0 := eq589090 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589090
  have eq594620 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ x = X1 ∨ x = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq462728 X1 (σ (M.op (τ X1) (τ X0)))
       have i₂ := eq589091 X1 X0
       grind)
    | exact superpose eq589091 eq462728
    | (have j0 := eq462728 X1 X1
       have j1 := eq589091 X1 X1
       grind)
    | exact resolve eq462728 eq589091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462728 eq589091
  have eq594681 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ x = X1 := by
    intro X0 X1
    first
    | (have j0 := eq594620 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594620
  have eq760092 : ∀ X0 X1 X3 : G, (M.op X1 (σ X0)) = X1 ∨ (M.op (τ X0) X3) = (k X3 (τ X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1912 x X1
       have i₂ := eq289903 x X0 X3
       grind)
    | (have i₁ := eq1912 X0 X1
       have i₂ := eq289903 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq289903 eq1912
    | (have j1 := eq289903 X0 X0 X3
       grind)
    | exact resolve eq1912 eq289903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1912 eq289903
  have eq1098642 : ∀ X0 X1 X2 : G, (τ (M.op X1 X1)) = (σ (M.op x (σ X0))) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1500 (σ X0) X1
       have i₂ := eq380836 X0 (σ X0) X2
       grind)
    | exact superpose eq380836 eq1500
    | (have j1 := eq380836 X0 X1 X2
       grind)
    | exact resolve eq1500 eq380836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1500 eq380836
  have eq1098733 : ∀ X0 X2 : G, (τ (σ x)) = (σ (M.op x (σ X0))) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq1098642 X0 x X2
       have i₂ := eq301880 x
       grind)
    | exact superpose eq301880 eq1098642
    | (have j0 := eq1098642 X0 x X2
       grind)
    | exact resolve eq1098642 eq301880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301880 eq1098642
  have eq1098793 : ∀ X0 X2 : G, x = (σ (M.op x (σ X0))) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq1098733 X0 X2
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq1098733
    | (have j0 := eq1098733 X0 X2
       grind)
    | exact resolve eq1098733 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098733
  have eq1099008 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ x = (σ (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1098793 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1098793
    | (have j0 := eq1098793 (τ X0) X1
       grind)
    | exact resolve eq1098793 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098793
  have eq1161902 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (k X0 (τ y)) = (M.op (τ y) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq760092 y (σ x) X0
       grind)
    | exact superpose eq760092 eq14
    | (have j1 := eq760092 y x X0
       grind)
    | exact resolve eq14 eq760092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760092
  have eq1161942 : ∀ X0 : G, x ≠ (σ (M.op x y)) ∨ (k X0 (τ y)) = (M.op (τ y) X0) := by
    intro X0
    first
    | (have i₁ := eq1161902 X0
       have i₂ := eq302529
       grind)
    | exact superpose eq302529 eq1161902
    | (have j0 := eq1161902 X0
       grind)
    | exact resolve eq1161902 eq302529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302529 eq1161902
  have eq1161994 : ∀ X0 : G, (k X0 (τ y)) = (M.op (τ y) X0) := by
    intro X0
    first
    | (have j0 := eq1161942 X0
       have j1 := eq1099008 y X0
       grind)
    | (have r₁ := eq1161942 X0
       have r₂ := eq1099008 y x
       grind)
    | exact resolve eq1161942 eq1099008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099008 eq1161942
  have eq1162931 : ∀ X0 : G, (τ (k X0 y)) = (M.op (τ y) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq33 y X0
       have i₂ := eq1161994 (τ X0)
       grind)
    | exact superpose eq1161994 eq33
    | exact resolve eq33 eq1161994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq1161994
  have eq1163164 : ∀ X0 : G, (τ (M.op y X0)) = (M.op (τ y) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1162931 X0
       have i₂ := eq411577 X0
       grind)
    | exact superpose eq411577 eq1162931
    | exact resolve eq1162931 eq411577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411577 eq1162931
  have eq1164337 : ∀ X0 X1 : G, (M.op X1 (τ (M.op y X0))) = (M.op (τ X0) (M.op (τ y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3263 (τ y) X1 (τ X0)
       have i₂ := eq1163164 X0
       grind)
    | exact superpose eq1163164 eq3263
    | exact resolve eq3263 eq1163164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3263
  have eq1164378 : ∀ X0 : G, (M.op x (τ X0)) = (M.op (τ (M.op y X0)) (τ y)) := by
    intro X0
    first
    | (have i₁ := eq302283 (τ y) (τ X0)
       have i₂ := eq1163164 X0
       grind)
    | exact superpose eq1163164 eq302283
    | exact resolve eq302283 eq1163164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302283
  have eq1166812 : ∀ X0 : G, (σ (M.op x (τ X0))) = (M.op (M.op y X0) y) ∨ x = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq594681 y (M.op y X0)
       have i₂ := eq1164378 X0
       grind)
    | exact superpose eq1164378 eq594681
    | (have j0 := eq594681 X0 (M.op y X0)
       grind)
    | exact resolve eq594681 eq1164378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594681 eq1164378
  have eq1166895 : ∀ X0 : G, (M.op (σ x) X0) = (σ (M.op x (τ X0))) ∨ x = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq1166812 X0
       have i₂ := eq302007 X0 y
       grind)
    | exact superpose eq302007 eq1166812
    | (have j0 := eq1166812 X0
       grind)
    | exact resolve eq1166812 eq302007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302007 eq1166812
  have eq1166995 : ∀ X0 : G, (M.op x X0) = (σ (M.op x (τ X0))) ∨ x = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq1166895 X0
       have i₂ := eq302486 X0
       grind)
    | exact superpose eq302486 eq1166895
    | (have j0 := eq1166895 X0
       grind)
    | exact resolve eq1166895 eq302486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166895
  have eq1168616 : ∀ X0 X1 : G, (M.op (τ X0) (τ (M.op y X1))) = (M.op (τ X1) (τ (M.op y X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1164337 X1 (τ X0)
       have i₂ := eq1163164 X0
       grind)
    | exact superpose eq1163164 eq1164337
    | exact resolve eq1164337 eq1163164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163164 eq1164337
  have eq1170331 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) ∨ x = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1166995 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1166995
    | (have j0 := eq1166995 (σ X0)
       grind)
    | exact resolve eq1166995 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166995
  have eq1298621 : ∀ X0 X1 : G, (M.op (τ X1) (τ X0)) = (M.op (τ (M.op y X0)) (τ (M.op y X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1168616 (M.op y X0) X1
       have i₂ := eq140 y X0
       grind)
    | exact superpose eq140 eq1168616
    | exact resolve eq1168616 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168616
  have eq1337391 : (M.op x (σ y)) ≠ (M.op x (σ y)) ∨ x = (M.op y (σ y)) := by
    first
    | (have i₁ := eq306510
       have i₂ := eq1170331 y
       grind)
    | exact superpose eq1170331 eq306510
    | (have j1 := eq1170331 y
       grind)
    | (have r₁ := eq306510
       have r₂ := eq1170331 y
       grind)
    | exact resolve eq306510 eq1170331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306510 eq1170331
  have eq1337412 : x = (M.op y (σ y)) := by grind
  clear eq1337391
  have eq1337495 : ∀ X0 : G, (M.op (τ (M.op y X0)) (τ x)) = (M.op (τ (σ y)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1298621 X0 (σ y)
       have i₂ := eq1337412
       grind)
    | exact superpose eq1337412 eq1298621
    | exact resolve eq1298621 eq1337412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298621
  have eq1337570 : (σ y) = (M.op y x) := by
    first
    | (have i₁ := eq140 y (σ y)
       have i₂ := eq1337412
       grind)
    | exact superpose eq1337412 eq140
    | exact resolve eq140 eq1337412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337412
  have eq1338732 : y = (σ y) := by
    first
    | (have i₁ := eq1337570
       have i₂ := eq302323 y
       grind)
    | exact superpose eq302323 eq1337570
    | exact resolve eq1337570 eq302323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302323 eq1337570
  have eq1338804 : ∀ X0 : G, (M.op y (τ X0)) = (M.op (τ (M.op y X0)) (τ x)) := by
    intro X0
    first
    | (have i₁ := eq1337495 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1337495
    | exact resolve eq1337495 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337495
  have eq1339366 : ∀ X0 : G, (M.op y (τ X0)) = (τ (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq1338804 X0
       have i₂ := eq302321 (τ (M.op y X0))
       grind)
    | exact superpose eq302321 eq1338804
    | exact resolve eq1338804 eq302321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302321 eq1338804
  have eq1339947 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1338732
       grind)
    | exact superpose eq1338732 eq14
    | exact resolve eq14 eq1338732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1340148 : y = (k y (τ (M.op y (M.op x y)))) := by
    first
    | (have i₁ := eq457324 y
       have i₂ := eq1338732
       grind)
    | exact superpose eq1338732 eq457324
    | exact resolve eq457324 eq1338732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457324
  have eq1340613 : y = (k y (M.op y (τ (M.op x y)))) := by
    first
    | (have i₁ := eq1340148
       have i₂ := eq1339366 (M.op x y)
       grind)
    | exact superpose eq1339366 eq1340148
    | exact resolve eq1340148 eq1339366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339366 eq1340148
  have eq1340697 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1339947
       have i₂ := eq302486 y
       grind)
    | exact superpose eq302486 eq1339947
    | exact resolve eq1339947 eq302486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302486 eq1339947
  have eq1395206 : y = (M.op x (τ (M.op x y))) ∨ y = (τ (M.op x y)) := by
    first
    | (have i₁ := eq366598 (τ (M.op x y)) y
       have i₂ := eq1340613
       grind)
    | exact superpose eq1340613 eq366598
    | (have j0 := eq366598 y (M.op x (τ (M.op x y)))
       grind)
    | exact resolve eq366598 eq1340613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366598 eq1340613
  have eq1504934 : (M.op x y) = (τ (M.op x y)) ∨ y = (τ (M.op x y)) := by
    first
    | (have i₁ := eq140 x (τ (M.op x y))
       have i₂ := eq1395206
       grind)
    | exact superpose eq1395206 eq140
    | exact resolve eq140 eq1395206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq1395206
  have eq1511185 : (M.op x y) = (σ (M.op x y)) ∨ y = (τ (M.op x y)) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq1504934
       grind)
    | exact superpose eq1504934 eq10
    | exact resolve eq10 eq1504934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504934
  have eq1511188 : y = (τ (M.op x y)) := by
    first
    | (have r₁ := eq1511185
       have r₂ := eq1340697
       grind)
    | exact resolve eq1511185 eq1340697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511185
  have eq1511262 : (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq1511188
       grind)
    | exact superpose eq1511188 eq10
    | exact resolve eq10 eq1511188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511188
  have eq1511788 : y = (M.op x y) := by
    first
    | (have i₁ := eq1511262
       have i₂ := eq1338732
       grind)
    | exact superpose eq1338732 eq1511262
    | exact resolve eq1511262 eq1338732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511262
  have eq1512068 : y ≠ (σ y) := by
    first
    | (have i₁ := eq1340697
       have i₂ := eq1511788
       grind)
    | exact superpose eq1511788 eq1340697
    | exact resolve eq1340697 eq1511788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340697 eq1511788
  have eq1513122 : False := by grind
  exact eq1513122
