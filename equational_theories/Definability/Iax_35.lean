import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation655`: `x = x ◇ (y ◇ ((z ◇ y) ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_x_pyy_pxy_Equation655 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law655 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law655.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X1) X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X2) X3)) (M.op X0 X0))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 (M.op X2 (M.op (M.op X3 X2) X3)) X0
       have i₂ := eq8 X0 X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 (M.op (M.op X0 (M.op (M.op X1 X0) X1)) X2))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X2 (M.op X0 (M.op (M.op X1 X0) X1))
       have i₂ := eq8 (M.op (M.op X0 (M.op (M.op X1 X0) X1)) X2) X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
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
  clear eq16
  have eq31 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 (M.op (M.op X2 X1) X2))) = (M.op (M.op X1 (M.op (M.op X2 X1) X2)) (M.op X1 (M.op (M.op X2 X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 (M.op X1 (M.op (M.op X2 X1) X2))
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 X0 (M.op X1 (M.op (M.op X2 X1) X2))
       grind)
    | (have r₁ := eq11 X0 (M.op X1 (M.op (M.op X2 X1) X2))
       have r₂ := eq8 X0 X1 X2
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op (M.op X2 X1) X2))) = (M.op (M.op X1 (M.op (M.op X2 X1) X2)) (M.op X1 (M.op (M.op X2 X1) X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq31 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq33 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X2)) = (k X0 (M.op X1 (M.op (M.op X2 X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 X0 X1 X2
       have i₂ := eq8 (M.op X1 (M.op (M.op X2 X1) X2)) X1 X2
       grind)
    | exact superpose eq8 eq32
    | exact resolve eq32 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq97 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 x x (M.op X0 X0) X1
       have i₂ := eq21 X0 (M.op X0 X0) x x
       grind)
    | exact superpose eq21 eq22
    | exact resolve eq22 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq22
  have eq125 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 X1)) = (M.op (M.op X1 X1) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X1 X1)
       have i₂ := eq97 X1 X0
       grind)
    | exact superpose eq97 eq11
    | (have j0 := eq11 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq11 X1 (M.op X0 X0)
       have r₂ := eq97 X0 X1
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = (M.op (M.op X1 X1) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq125 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq137 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq133 X0 X1
       have i₂ := eq97 X1 (M.op X1 X1)
       grind)
    | exact superpose eq97 eq133
    | exact resolve eq133 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq152 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op (M.op X1 X0) X1))) = (k X2 (σ (M.op X0 (M.op (M.op X1 X0) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (M.op X0 (M.op (M.op X1 X0) X1))
       have i₂ := eq33 (τ X2) X0 X1
       grind)
    | exact superpose eq33 eq15
    | exact resolve eq15 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq33
  have eq164 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (M.op X0 X0)
       have i₂ := eq137 (σ X1) X0
       grind)
    | exact superpose eq137 eq28
    | exact resolve eq28 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq137
  have eq173 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq43 x y
       grind)
    | exact superpose eq43 eq14
    | (have j1 := eq43 x y
       grind)
    | exact resolve eq14 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq622 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq182 (τ X0) (τ X1)
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq182
    | (have j0 := eq182 (τ X0) (τ X1)
       grind)
    | exact resolve eq182 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq182
  have eq629 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq622 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq622
    | (have j0 := eq622 X0 X1
       grind)
    | exact resolve eq622 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq633 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq629 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq629
    | (have j0 := eq629 X0 X1
       grind)
    | exact resolve eq629 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq636 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq633 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq633
    | (have j0 := eq633 X0 X1
       grind)
    | exact resolve eq633 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq637 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq636 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq636
    | (have j0 := eq636 X0 X1
       grind)
    | exact resolve eq636 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq746 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq173
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq173
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq173 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq747 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq746
  have eq754 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ x)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8 X0 (σ y) (σ x)
       have i₂ := eq747
       grind)
    | exact superpose eq747 eq8
    | exact resolve eq8 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq756 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq754 X0
       have i₂ := eq97 (σ x) (σ y)
       grind)
    | exact superpose eq97 eq754
    | exact resolve eq754 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq796 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq164 (σ y) x
       have i₂ := eq756 (σ y)
       grind)
    | exact superpose eq756 eq164
    | exact resolve eq164 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq756
  have eq825 : ∀ X0 : G, y = (k X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq796 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq796
    | exact resolve eq796 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796
  have eq1008 : ∀ X0 : G, y ≠ X0 ∨ (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq637 X0 y
       have i₂ := eq825 X0
       grind)
    | exact superpose eq825 eq637
    | (have j0 := eq637 X0 y
       grind)
    | (have r₁ := eq637 y y
       have r₂ := eq825 y
       grind)
    | exact resolve eq637 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq2859 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq1008 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq3256 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq97 y X0
       have i₂ := eq2859
       grind)
    | exact superpose eq2859 eq97
    | exact resolve eq97 eq2859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2859
  have eq3923 : x ≠ x ∨ x = (M.op x y) := by
    first
    | (have j0 := eq3256 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3256
  have eq3924 : x = (M.op x y) := by grind
  clear eq3923
  have eq4504 : ∀ X0 : G, (M.op X0 (M.op y (M.op x x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 y x
       have i₂ := eq3924
       grind)
    | exact superpose eq3924 eq8
    | exact resolve eq8 eq3924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4518 : ∀ X0 : G, (σ (M.op y (M.op x x))) = (k X0 (σ (M.op y (M.op x x)))) := by
    intro X0
    first
    | (have i₁ := eq152 y x x
       have i₂ := eq3924
       grind)
    | exact superpose eq3924 eq152
    | exact resolve eq152 eq3924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq3924
  have eq4520 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq4518 X0
       have i₂ := eq97 x y
       grind)
    | exact superpose eq97 eq4518
    | exact resolve eq4518 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4518
  have eq4533 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq4504 X0
       have i₂ := eq97 x y
       grind)
    | exact superpose eq97 eq4504
    | exact resolve eq4504 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4504
  have eq5581 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq637 X0 (σ y)
       have i₂ := eq4520 X0
       grind)
    | exact superpose eq4520 eq637
    | (have j0 := eq637 X0 (σ y)
       grind)
    | (have r₁ := eq637 (σ y) (σ y)
       have r₂ := eq4520 (σ y)
       grind)
    | exact resolve eq637 eq4520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637 eq4520
  have eq7369 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have j0 := eq5581 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5581
  have eq7439 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq97 (σ y) X0
       have i₂ := eq7369
       grind)
    | exact superpose eq7369 eq97
    | exact resolve eq97 eq7369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq7369
  have eq7698 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq7439 (σ x)
       grind)
    | exact superpose eq7439 eq14
    | exact resolve eq14 eq7439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7439
  have eq7702 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq7698
       have i₂ := eq4533 x
       grind)
    | exact superpose eq4533 eq7698
    | exact resolve eq7698 eq4533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4533 eq7698
  have eq7703 : False := by grind
  exact eq7703

/-- `Equation658`: `x = x ◇ (y ◇ ((z ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_pxx_pyx_Equation658 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law658 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law658.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X2) X1))) = X0 := by
    intro X0 X1 X2
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
  clear eq15
  have eq23 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X0) (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op (M.op X0 X0) (M.op X1 X1)) X1
       have i₂ := eq8 (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X1 X1) X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (k X0 X2) = (M.op X2 X0) := by
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
  have eq46 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq48 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
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
  have eq50 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq43 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq72 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0) x
       have i₂ := eq23 x X0 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq8
    | exact resolve eq8 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq87 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0) X1
       have i₂ := eq72 X0 (M.op X0 X0)
       grind)
    | exact superpose eq72 eq11
    | (have r₁ := eq11 (M.op X0 X0) X1
       have r₂ := eq72 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq103 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq50 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq50 eq13
    | (have j1 := eq50 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq117 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0)
       have i₂ := eq91 X0 (τ X1)
       grind)
    | exact superpose eq91 eq16
    | exact resolve eq16 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq432 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq46 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq1077 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq1142 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1077 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1077
    | (have j0 := eq1077 X0 X1
       grind)
    | exact resolve eq1077 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq1193 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X0) X1) ∨ (σ (k X0 X2)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq117 X1 X1
       have i₂ := eq1142 X0 X1
       grind)
    | exact superpose eq1142 eq117
    | (have j1 := eq1142 X2 X0
       grind)
    | exact resolve eq117 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq1142
  have eq2217 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq432 (M.op X0 X0)
       have i₂ := eq91 X0 (M.op X0 X0)
       grind)
    | exact superpose eq91 eq432
    | (have j0 := eq432 (M.op X0 X0)
       grind)
    | exact resolve eq432 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq2231 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq432 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq432
    | (have j0 := eq432 (τ X0)
       grind)
    | exact resolve eq432 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq432
  have eq2244 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq2217 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2217
  have eq2251 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2231 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2231
    | (have j0 := eq2231 X0
       grind)
    | exact resolve eq2231 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2231
  have eq2260 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2251 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2251
    | (have j0 := eq2251 X0
       grind)
    | exact resolve eq2251 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2251
  have eq2732 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq72 (σ (M.op X0 X0)) X1
       have i₂ := eq2244 X0
       grind)
    | exact superpose eq2244 eq72
    | exact resolve eq72 eq2244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2244
  have eq3041 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq103 x y X0
       grind)
    | exact superpose eq103 eq14
    | (have j1 := eq103 X0 y X0
       grind)
    | exact resolve eq14 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq3123 : ∀ X0 : G, (σ y) = (k (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq3041 X0
       have j1 := eq1193 y X0 x
       grind)
    | (have r₁ := eq3041 X0
       have r₂ := eq1193 y x x
       grind)
    | exact resolve eq3041 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193 eq3041
  have eq3173 : ∀ X0 : G, (τ (σ y)) = (k (τ (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq20 (σ y) X0
       have i₂ := eq3123 (σ X0)
       grind)
    | exact superpose eq3123 eq20
    | exact resolve eq20 eq3123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3123
  have eq3177 : ∀ X0 : G, y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq3173 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3173
    | exact resolve eq3173 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3173
  have eq3309 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2260 y
       have i₂ := eq3177 y
       grind)
    | exact superpose eq3177 eq2260
    | (have j0 := eq2260 y
       grind)
    | (have r₁ := eq2260 y
       have r₂ := eq3177 y
       grind)
    | exact resolve eq2260 eq3177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2260 eq3177
  have eq3329 : y = (M.op y y) := by grind
  clear eq3309
  have eq3447 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq72 y X0
       have i₂ := eq3329
       grind)
    | exact superpose eq3329 eq72
    | exact resolve eq72 eq3329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq3461 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2732 y X0
       have i₂ := eq3329
       grind)
    | exact superpose eq3329 eq2732
    | exact resolve eq2732 eq3329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2732 eq3329
  have eq4020 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq3461 (σ x)
       grind)
    | exact superpose eq3461 eq14
    | exact resolve eq14 eq3461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3461
  have eq4028 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq4020
       have i₂ := eq3447 x
       grind)
    | exact superpose eq3447 eq4020
    | exact resolve eq4020 eq3447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3447 eq4020
  have eq4029 : False := by grind
  exact eq4029

/-- `Equation658`: `x = x ◇ (y ◇ ((z ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pxx_pxy_Equation658 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law658 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law658.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X2) X1))) = X0 := by
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
  have eq18 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq13
    | exact resolve eq13 eq15
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
  have eq23 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X0) (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op (M.op X0 X0) (M.op X1 X1)) X1
       have i₂ := eq8 (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X1 X1) X0
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
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq32 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X0)) ≠ (M.op X0 (M.op (M.op X1 X1) X0)) ∨ (M.op X2 X2) = (k X2 (M.op X0 (M.op (M.op X1 X1) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X2 (M.op X0 (M.op (M.op X1 X1) X0))
       have i₂ := eq8 (M.op X0 (M.op (M.op X1 X1) X0)) X0 X1
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 X2 (M.op X0 (M.op (M.op X1 X1) X0))
       grind)
    | (have r₁ := eq11 X0 (M.op X1 (M.op (M.op X2 X2) X1))
       have r₂ := eq8 (M.op X1 (M.op (M.op X2 X2) X1)) X1 X2
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X2 (M.op X0 (M.op (M.op X1 X1) X0))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq32 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq43 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
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
  have eq46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq47 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq43 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq66 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X2 X2))) = X1 ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X0 X2 X1
       have i₂ := eq12 X3 X0
       grind)
    | exact superpose eq12 eq23
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq23 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0) x
       have i₂ := eq23 x X0 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq8
    | exact resolve eq8 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq79 : ∀ X0 X1 X3 : G, (M.op X1 X0) = X1 ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq66 X0 X1 x X3
       have i₂ := eq72 x X0
       grind)
    | exact superpose eq72 eq66
    | (have j0 := eq66 X0 X1 x X3
       grind)
    | exact resolve eq66 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq87 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X0)
       have i₂ := eq72 X0 (M.op X0 X0)
       grind)
    | exact superpose eq72 eq11
    | (have j0 := eq11 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq72 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq95 : ∀ X0 X1 X2 X3 X4 : G, (k X0 (M.op X1 (M.op (M.op X2 X2) X1))) = (k X0 (M.op X3 (M.op (M.op X4 X4) X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq33 X3 X4 X0
       have i₂ := eq33 X1 X2 X0
       grind)
    | exact superpose eq33 eq33
    | exact resolve eq33 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (M.op (M.op X2 X2) X1)))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 (M.op X1 (M.op (M.op X2 X2) X1))
       have i₂ := eq33 X1 X2 (τ X0)
       grind)
    | exact superpose eq33 eq15
    | exact resolve eq15 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq136 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X1)) = (k X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq91 X2 X0
       have i₂ := eq91 X1 X0
       grind)
    | exact superpose eq91 eq91
    | exact resolve eq91 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 X1 X2 : G, (M.op X2 (k X0 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 X0 X2
       have i₂ := eq91 X1 X0
       grind)
    | exact superpose eq91 eq72
    | exact resolve eq72 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (M.op X1 X1)
       have i₂ := eq91 X1 (σ X0)
       grind)
    | exact superpose eq91 eq29
    | exact resolve eq29 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq470 : ∀ X0 X1 X2 X3 : G, (k X2 (k X0 (M.op X1 X1))) = (k X2 (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq136 X2 X3 (k X0 (M.op X1 X1))
       have i₂ := eq153 X0 X1 (k X0 (M.op X1 X1))
       grind)
    | exact superpose eq153 eq136
    | exact resolve eq136 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq718 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 (σ X0) X1
       have i₂ := eq46 X2 X0
       grind)
    | exact superpose eq46 eq72
    | (have j1 := eq46 X2 X0
       grind)
    | exact resolve eq72 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq799 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq79 (σ y) (σ x) X0
       grind)
    | exact superpose eq79 eq14
    | (have j1 := eq79 (σ y) x X0
       grind)
    | exact resolve eq14 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1267 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq210 (M.op X0 X0) X1
       have i₂ := eq72 X0 (M.op X0 X0)
       grind)
    | exact superpose eq72 eq210
    | (have j0 := eq210 (M.op X0 X0) X1
       grind)
    | exact resolve eq210 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1276 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) ≠ (k X0 (M.op X1 X1)) ∨ (k X0 X0) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq210 X1 X1
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq210
    | exact resolve eq210 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1291 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq210 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1295 : ∀ X0 X1 : G, (k X0 X0) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1276 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276
  have eq1311 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1267 X0 X1
       have j1 := eq79 X1 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq1267 X0 X0
       have r₂ := eq79 X0 (M.op X0 X0) x
       grind)
    | exact resolve eq1267 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267
  have eq1339 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq1291 (σ X0)
       grind)
    | exact superpose eq1291 eq13
    | exact resolve eq13 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1341 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq1291 (τ X0)
       grind)
    | exact superpose eq1291 eq34
    | exact resolve eq34 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1344 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1341 X0
       have i₂ := eq1291 X0
       grind)
    | exact superpose eq1291 eq1341
    | exact resolve eq1341 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341
  have eq1346 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1339 X0
       have i₂ := eq1291 X0
       grind)
    | exact superpose eq1291 eq1339
    | exact resolve eq1339 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339
  have eq1498 : ∀ X0 X1 : G, (k (τ X0) (M.op X1 X1)) = (τ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq1295 (τ X0) X1
       grind)
    | exact superpose eq1295 eq34
    | exact resolve eq34 eq1295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1295
  have eq1522 : ∀ X0 X1 : G, (k (τ X0) (M.op X1 X1)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1498 X0 X1
       have i₂ := eq1291 X0
       grind)
    | exact superpose eq1291 eq1498
    | exact resolve eq1498 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1291 eq1498
  have eq1603 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq72 (τ X0) X1
       have i₂ := eq1344 X0
       grind)
    | exact superpose eq1344 eq72
    | exact resolve eq72 eq1344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1608 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (τ X0) X1
       have i₂ := eq1344 X0
       grind)
    | exact superpose eq1344 eq91
    | exact resolve eq91 eq1344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2035 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq72 (σ X0) X1
       have i₂ := eq1346 X0
       grind)
    | exact superpose eq1346 eq72
    | exact resolve eq72 eq1346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2040 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (σ X0) X1
       have i₂ := eq1346 X0
       grind)
    | exact superpose eq1346 eq91
    | exact resolve eq91 eq1346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq1346
  have eq2077 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq2196 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2077 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2077
    | (have j0 := eq2077 X0 X1
       grind)
    | exact resolve eq2077 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2077
  have eq4679 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X1 X1)
       have i₂ := eq2040 X1 (σ X0)
       grind)
    | exact superpose eq2040 eq13
    | exact resolve eq13 eq2040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040
  have eq6544 : ∀ X0 X1 X2 : G, (σ (k X0 (M.op X1 (M.op (M.op X2 X2) X1)))) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X1 (M.op (M.op X2 X2) X1))
       have i₂ := eq123 (σ X0) X1 X2
       grind)
    | exact superpose eq123 eq13
    | exact resolve eq13 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq6596 : ∀ X0 X1 X2 : G, (σ (k X0 (M.op X1 (M.op (M.op X2 X2) X1)))) = (σ (τ (M.op (σ X0) (σ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6544 X0 X1 X2
       have i₂ := eq1344 (σ X0)
       grind)
    | exact superpose eq1344 eq6544
    | exact resolve eq6544 eq1344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1344 eq6544
  have eq6722 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (M.op X1 (M.op (M.op X2 X2) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6596 X0 X1 X2
       have i₂ := eq10 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq10 eq6596
    | exact resolve eq6596 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6596
  have eq7950 : ∀ X0 X1 X2 X3 : G, (M.op (k X0 (M.op X1 (M.op (M.op X2 X2) X1))) X3) = (k (k X0 (M.op X1 (M.op (M.op X2 X2) X1))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1311 X2 X1
       have i₂ := eq33 X0 X1 X2
       grind)
    | exact superpose eq33 eq1311
    | exact resolve eq1311 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq128321 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2035 X0 X1
       have i₂ := eq2196 X2 X0
       grind)
    | exact superpose eq2196 eq2035
    | (have j1 := eq2196 X2 X0
       grind)
    | exact resolve eq2035 eq2196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2035 eq2196
  have eq153553 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq718 y X0 x
       grind)
    | exact superpose eq718 eq14
    | (have j1 := eq718 y X0 x
       grind)
    | exact resolve eq14 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq154068 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq153553 X0
       have j1 := eq128321 y X0 x
       grind)
    | (have r₁ := eq153553 X0
       have r₂ := eq128321 y x x
       grind)
    | exact resolve eq153553 eq128321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128321 eq153553
  have eq154527 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = (k X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq136 X0 (σ y) X1
       have i₂ := eq154068 (σ y)
       grind)
    | exact superpose eq154068 eq136
    | exact resolve eq136 eq154068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq154535 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq160 X0 (σ y)
       have i₂ := eq154068 (σ y)
       grind)
    | exact superpose eq154068 eq160
    | exact resolve eq160 eq154068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq154585 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1522 X0 (σ y)
       have i₂ := eq154068 (σ y)
       grind)
    | exact superpose eq154068 eq1522
    | exact resolve eq1522 eq154068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1522
  have eq154590 : ∀ X0 : G, (M.op X0 (τ (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1603 (σ y) X0
       have i₂ := eq154068 (σ y)
       grind)
    | exact superpose eq154068 eq1603
    | exact resolve eq1603 eq154068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1603
  have eq154591 : ∀ X0 : G, (M.op X0 X0) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq1608 (σ y) X0
       have i₂ := eq154068 (σ y)
       grind)
    | exact superpose eq154068 eq1608
    | exact resolve eq1608 eq154068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1608
  have eq154693 : ∀ X0 X1 X2 X3 : G, (k X1 (M.op X2 (M.op (M.op X3 X3) X2))) = (k X1 (M.op (σ y) (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq95 X1 X2 X3 (σ y) X0
       have i₂ := eq154068 (M.op X0 X0)
       grind)
    | exact superpose eq154068 eq95
    | exact resolve eq95 eq154068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq154757 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq154068 (σ x)
       grind)
    | exact superpose eq154068 eq14
    | exact resolve eq14 eq154068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154865 : ∀ X1 X2 X3 : G, (k X1 (M.op X2 (M.op (M.op X3 X3) X2))) = (k X1 (σ y)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq154693 x X1 X2 X3
       have i₂ := eq72 x (σ y)
       grind)
    | exact superpose eq72 eq154693
    | exact resolve eq154693 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq154693
  have eq154910 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq154591 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq154591
    | exact resolve eq154591 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154591
  have eq154911 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq154590 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq154590
    | exact resolve eq154590 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154590
  have eq154932 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq154535 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq154535
    | exact resolve eq154535 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154535
  have eq154990 : ∀ X0 : G, (k X0 y) = (k (τ (σ X0)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq154932 X0
       have i₂ := eq154585 (σ X0)
       grind)
    | exact superpose eq154585 eq154932
    | exact resolve eq154932 eq154585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154585 eq154932
  have eq155007 : ∀ X0 : G, (k X0 (σ y)) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq154990 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq154990
    | exact resolve eq154990 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154990
  have eq155077 : ∀ X0 X1 X2 : G, (k X0 (M.op X2 X2)) = (k X0 (k X1 y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq470 X1 y X0 X2
       have i₂ := eq154911 y
       grind)
    | exact superpose eq154911 eq470
    | exact resolve eq470 eq154911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq155174 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq4679 X0 y
       have i₂ := eq154911 y
       grind)
    | exact superpose eq154911 eq4679
    | exact resolve eq4679 eq154911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4679
  have eq155292 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq799 X0
       have i₂ := eq154911 x
       grind)
    | exact superpose eq154911 eq799
    | (have j0 := eq799 X0
       grind)
    | exact resolve eq799 eq154911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799 eq154911
  have eq155293 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq155292 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155292
  have eq155298 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq155293 X0
       have i₂ := eq154068 X0
       grind)
    | exact superpose eq154068 eq155293
    | exact resolve eq155293 eq154068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154068 eq155293
  have eq155369 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) y) := by
    intro X0
    first
    | (have i₁ := eq155174 X0
       have i₂ := eq154910 (σ X0)
       grind)
    | exact superpose eq154910 eq155174
    | exact resolve eq155174 eq154910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155174
  have eq155389 : ∀ X0 X1 : G, (k X0 (σ y)) = (k X0 (k X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq155077 X0 X1 x
       have i₂ := eq154527 X0 x
       grind)
    | exact superpose eq154527 eq155077
    | exact resolve eq155077 eq154527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154527 eq155077
  have eq155444 : ∀ X0 X1 : G, (k X0 y) = (k X0 (k X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq155389 X0 X1
       have i₂ := eq155007 X0
       grind)
    | exact superpose eq155007 eq155389
    | exact resolve eq155389 eq155007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155389
  have eq158614 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (k X1 (k (τ X0) y))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 y X1
       have i₂ := eq155298 X0
       grind)
    | exact superpose eq155298 eq18
    | exact resolve eq18 eq155298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq158705 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq155298 (σ X0)
       grind)
    | exact superpose eq155298 eq13
    | exact resolve eq13 eq155298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158708 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (σ y)
       have i₂ := eq155298 (σ X0)
       grind)
    | exact superpose eq155298 eq29
    | exact resolve eq29 eq155298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq155298
  have eq158738 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq158708 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq158708
    | exact resolve eq158708 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158708
  have eq158758 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (k X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq158614 X0 X1
       have i₂ := eq155444 X1 (τ X0)
       grind)
    | exact superpose eq155444 eq158614
    | exact resolve eq158614 eq155444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155444 eq158614
  have eq158774 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq158738 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq158738
    | exact resolve eq158738 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158738
  have eq158781 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq158758 X0 X1
       have i₂ := eq158705 X1
       grind)
    | exact superpose eq158705 eq158758
    | exact resolve eq158758 eq158705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158758
  have eq159995 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) X3) ≠ (σ (k X0 (M.op X1 (M.op (M.op X2 X2) X1)))) ∨ (M.op (σ X0) X3) = (k (σ X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq210 (σ X0) X3
       have i₂ := eq6722 X0 X1 X2
       grind)
    | exact superpose eq6722 eq210
    | (have j0 := eq210 (σ X0) X3
       grind)
    | exact resolve eq210 eq6722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq160176 : ∀ X0 X1 X2 X3 : G, (k (M.op (σ X0) (σ X0)) (σ X3)) = (σ (k (k X0 (M.op X1 (M.op (M.op X2 X2) X1))) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (k X0 (M.op X1 (M.op (M.op X2 X2) X1))) X3
       have i₂ := eq6722 X0 X1 X2
       grind)
    | exact superpose eq6722 eq13
    | exact resolve eq13 eq6722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6722
  have eq160287 : ∀ X0 X1 X2 X3 : G, (k (M.op (σ X0) (σ X0)) (σ X3)) = (σ (M.op (k X0 (M.op X1 (M.op (M.op X2 X2) X1))) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq160176 X0 X1 X2 X3
       have i₂ := eq7950 X0 X1 X2 X3
       grind)
    | exact superpose eq7950 eq160176
    | exact resolve eq160176 eq7950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7950 eq160176
  have eq160428 : ∀ X0 X3 : G, (M.op (σ X0) X3) ≠ (σ (k X0 (σ y))) ∨ (M.op (σ X0) X3) = (k (σ X0) X3) := by
    intro X0 X3
    first
    | (have i₁ := eq159995 X0 x x X3
       have i₂ := eq154865 X0 x x
       grind)
    | exact superpose eq154865 eq159995
    | (have j0 := eq159995 X0 x x X3
       grind)
    | exact resolve eq159995 eq154865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159995
  have eq160959 : ∀ X0 X3 : G, (k (M.op (σ X0) (σ X0)) (σ X3)) = (σ (M.op (k X0 (σ y)) X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq160287 X0 x x X3
       have i₂ := eq154865 X0 x x
       grind)
    | exact superpose eq154865 eq160287
    | exact resolve eq160287 eq154865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154865 eq160287
  have eq161040 : ∀ X0 X3 : G, (M.op (σ X0) X3) ≠ (σ (k X0 y)) ∨ (M.op (σ X0) X3) = (k (σ X0) X3) := by
    intro X0 X3
    first
    | (have i₁ := eq160428 X0 X3
       have i₂ := eq155007 X0
       grind)
    | exact superpose eq155007 eq160428
    | (have j0 := eq160428 X0 X3
       grind)
    | exact resolve eq160428 eq155007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160428
  have eq161451 : ∀ X0 X3 : G, (k (M.op (σ X0) (σ X0)) (σ X3)) = (σ (M.op (k X0 y) X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq160959 X0 X3
       have i₂ := eq155007 X0
       grind)
    | exact superpose eq155007 eq160959
    | exact resolve eq160959 eq155007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155007 eq160959
  have eq161526 : ∀ X0 X3 : G, (σ X0) ≠ (M.op (σ X0) X3) ∨ (M.op (σ X0) X3) = (k (σ X0) X3) := by
    intro X0 X3
    first
    | (have i₁ := eq161040 X0 X3
       have i₂ := eq158705 X0
       grind)
    | exact superpose eq158705 eq161040
    | (have j0 := eq161040 X0 X3
       grind)
    | exact resolve eq161040 eq158705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161040
  have eq161858 : ∀ X0 X3 : G, (k (M.op (σ X0) (σ X0)) (σ X3)) = (σ (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq161451 X0 X3
       have i₂ := eq158774 X0
       grind)
    | exact superpose eq158774 eq161451
    | exact resolve eq161451 eq158774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158774 eq161451
  have eq161882 : ∀ X0 X3 : G, (M.op (σ X0) X3) = (k (σ X0) X3) := by
    intro X0 X3
    first
    | (have j0 := eq161526 X0 X3
       have j1 := eq79 X3 x (σ X0)
       grind)
    | (have r₁ := eq161526 X0 X0
       have r₂ := eq79 X0 (σ X0) X3
       grind)
    | exact resolve eq161526 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq161526
  have eq162085 : ∀ X0 X3 : G, (M.op (M.op (σ X0) (σ X0)) (σ X3)) = (σ (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq161858 X0 X3
       have i₂ := eq1311 (σ X0) (σ X3)
       grind)
    | exact superpose eq1311 eq161858
    | exact resolve eq161858 eq1311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1311 eq161858
  have eq162101 : ∀ X0 X3 : G, (σ X0) = (M.op (σ X0) X3) := by
    intro X0 X3
    first
    | (have i₁ := eq161882 X0 X3
       have i₂ := eq158781 X3 X0
       grind)
    | exact superpose eq158781 eq161882
    | exact resolve eq161882 eq158781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158781 eq161882
  have eq162197 : ∀ X0 X3 : G, (σ (M.op X0 X3)) = (M.op (k (σ X0) y) (σ X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq162085 X0 X3
       have i₂ := eq154910 (σ X0)
       grind)
    | exact superpose eq154910 eq162085
    | exact resolve eq162085 eq154910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154910 eq162085
  have eq162266 : ∀ X0 X3 : G, (σ (M.op X0 X3)) = (M.op (σ (k X0 y)) (σ X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq162197 X0 X3
       have i₂ := eq155369 X0
       grind)
    | exact superpose eq155369 eq162197
    | exact resolve eq162197 eq155369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155369 eq162197
  have eq162310 : ∀ X0 X3 : G, (σ (M.op X0 X3)) = (σ (k X0 y)) := by
    intro X0 X3
    first
    | (have i₁ := eq162266 X0 X3
       have i₂ := eq162101 (k X0 y) (σ X3)
       grind)
    | exact superpose eq162101 eq162266
    | exact resolve eq162266 eq162101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162101 eq162266
  have eq162325 : ∀ X0 X3 : G, (σ X0) = (σ (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq162310 X0 X3
       have i₂ := eq158705 X0
       grind)
    | exact superpose eq158705 eq162310
    | exact resolve eq162310 eq158705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158705 eq162310
  have eq178933 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq154757
       have i₂ := eq162325 x y
       grind)
    | exact superpose eq162325 eq154757
    | (have r₁ := eq154757
       have r₂ := eq162325 x y
       grind)
    | exact resolve eq154757 eq162325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154757 eq162325
  have eq178934 : False := by grind
  exact eq178934

/-- `Equation658`: `x = x ◇ (y ◇ ((z ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pyy_pxy_Equation658 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law658 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law658.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X2) X1))) = X0 := by
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
  have eq23 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X0) (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op (M.op X0 X0) (M.op X1 X1)) X1
       have i₂ := eq8 (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X1 X1) X0
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
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
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
  have eq46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq47 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq43 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq72 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0) x
       have i₂ := eq23 x X0 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq8
    | exact resolve eq8 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq87 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X0 X0)
       have i₂ := eq72 X0 (M.op X0 X0)
       grind)
    | exact superpose eq72 eq11
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq72 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq103 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq50 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq50 eq13
    | (have j1 := eq50 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq118 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (M.op X0 X0)
       have i₂ := eq91 X0 (τ X1)
       grind)
    | exact superpose eq91 eq15
    | exact resolve eq15 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq432 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq46 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq1077 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq1142 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1077 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1077
    | (have j0 := eq1077 X0 X1
       grind)
    | exact resolve eq1077 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq1194 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq118 X1 X1
       have i₂ := eq1142 X0 X1
       grind)
    | exact superpose eq1142 eq118
    | (have j1 := eq1142 X2 X0
       grind)
    | exact resolve eq118 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq1142
  have eq2216 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq432 (M.op X0 X0)
       have i₂ := eq91 X0 (M.op X0 X0)
       grind)
    | exact superpose eq91 eq432
    | (have j0 := eq432 (M.op X0 X0)
       grind)
    | exact resolve eq432 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq2231 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq432 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq432
    | (have j0 := eq432 (τ X0)
       grind)
    | exact resolve eq432 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq432
  have eq2245 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq2216 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2216
  have eq2251 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2231 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2231
    | (have j0 := eq2231 X0
       grind)
    | exact resolve eq2231 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2231
  have eq2260 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2251 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2251
    | (have j0 := eq2251 X0
       grind)
    | exact resolve eq2251 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2251
  have eq2732 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq72 (σ (M.op X0 X0)) X1
       have i₂ := eq2245 X0
       grind)
    | exact superpose eq2245 eq72
    | exact resolve eq72 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2245
  have eq3039 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq103 x y X0
       grind)
    | exact superpose eq103 eq14
    | (have j1 := eq103 X0 y X0
       grind)
    | exact resolve eq14 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq3121 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq3039 X0
       have j1 := eq1194 y X0 x
       grind)
    | (have r₁ := eq3039 X0
       have r₂ := eq1194 y x x
       grind)
    | exact resolve eq3039 eq1194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194 eq3039
  have eq3169 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (σ y)
       have i₂ := eq3121 (σ X0)
       grind)
    | exact superpose eq3121 eq29
    | exact resolve eq29 eq3121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3121
  have eq3175 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq3169 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3169
    | exact resolve eq3169 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3169
  have eq3307 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2260 y
       have i₂ := eq3175 y
       grind)
    | exact superpose eq3175 eq2260
    | (have j0 := eq2260 y
       grind)
    | (have r₁ := eq2260 y
       have r₂ := eq3175 y
       grind)
    | exact resolve eq2260 eq3175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2260 eq3175
  have eq3327 : y = (M.op y y) := by grind
  clear eq3307
  have eq3443 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq72 y X0
       have i₂ := eq3327
       grind)
    | exact superpose eq3327 eq72
    | exact resolve eq72 eq3327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq3457 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2732 y X0
       have i₂ := eq3327
       grind)
    | exact superpose eq3327 eq2732
    | exact resolve eq2732 eq3327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2732 eq3327
  have eq4016 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq3457 (σ x)
       grind)
    | exact superpose eq3457 eq14
    | exact resolve eq14 eq3457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3457
  have eq4024 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq4016
       have i₂ := eq3443 x
       grind)
    | exact superpose eq3443 eq4016
    | exact resolve eq4016 eq3443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3443 eq4016
  have eq4025 : False := by grind
  exact eq4025

/-- `Equation677`: `x = y ◇ (x ◇ ((y ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation677 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law677 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law677.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq87 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq91 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq87 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq87 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq87 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq107 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq91 (σ X0) (σ X1)
       grind)
    | exact superpose eq91 eq13
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq107 X0 X1
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq107
    | exact resolve eq107 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq107
  have eq1497 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq114 x y
       grind)
    | exact superpose eq114 eq14
    | (have r₁ := eq14
       have r₂ := eq114 x y
       grind)
    | exact resolve eq14 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq1517 : False := by grind
  exact eq1517

/-- `Equation692`: `x = y ◇ (x ◇ ((z ◇ y) ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation692 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law692 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law692.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X2 X1) X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq22 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (M.op X0 X1) X0) X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 (M.op (M.op X0 X1) X0)
       have i₂ := eq8 (M.op (M.op (M.op X0 X1) X0) X2) X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq13
    | exact resolve eq13 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
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
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq57 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq125 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq129 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq125 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq125 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq125 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq125 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq148 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq129 (σ X0) (σ X1)
       grind)
    | exact superpose eq129 eq13
    | exact resolve eq13 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq148 X0 X1
       have i₂ := eq129 X0 X1
       grind)
    | exact superpose eq129 eq148
    | exact resolve eq148 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq428 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq57 x y
       grind)
    | exact superpose eq57 eq14
    | (have j1 := eq57 x y
       grind)
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq451 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq428
       have i₂ := eq129 x y
       grind)
    | exact superpose eq129 eq428
    | exact resolve eq428 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq428
  have eq452 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq451
  have eq497 : (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq452
       have i₂ := eq157 x y
       grind)
    | exact superpose eq157 eq452
    | exact resolve eq452 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq452
  have eq603 : (M.op x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq497
       grind)
    | exact superpose eq497 eq9
    | exact resolve eq9 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq622 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq603
       have i₂ := eq9 (M.op x x)
       grind)
    | exact superpose eq9 eq603
    | exact resolve eq603 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq755 : ∀ X0 : G, y = (M.op X0 (M.op (M.op (M.op x x) x) X0)) := by
    intro X0
    first
    | (have i₁ := eq22 x y X0
       have i₂ := eq622
       grind)
    | exact superpose eq622 eq22
    | exact resolve eq22 eq622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq758 : x = y := by
    first
    | (have i₁ := eq755 x
       have i₂ := eq22 x x x
       grind)
    | exact superpose eq22 eq755
    | exact resolve eq755 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq755
  have eq795 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq758
       grind)
    | exact superpose eq758 eq14
    | exact resolve eq14 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq796 : False := by grind
  exact eq796

/-- `Equation695`: `x = y ◇ (x ◇ ((z ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_pxx_pxy_Equation695 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law695 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law695.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X2 X2) X1))) = X0 := by
    intro X0 X1 X2
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
  clear eq15
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2))) (M.op X3 X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2))) X2
       have i₂ := eq8 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op (M.op X1 X1) X2) X0
       have i₂ := eq8 (M.op X0 X0) X2 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
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
  have eq40 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (k X0 X2) = (M.op X0 X2) := by
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
  have eq44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq48 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq40 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = X1 ∨ (k X0 X3) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 X2 X0 X1
       have i₂ := eq12 X0 X3
       grind)
    | exact superpose eq12 eq22
    | (have j1 := eq12 X0 X3
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X2 (M.op X0 X0) (M.op X1 X1)
       have i₂ := eq22 X1 X0 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (M.op X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X1 X1) (M.op X0 X0)
       have i₂ := eq22 X1 X0 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X1 X1) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (M.op X2 X2) (M.op (M.op X1 X1) X0)) (M.op (M.op X1 X1) X0) X2
       have i₂ := eq22 (M.op (M.op X2 X2) (M.op (M.op X1 X1) X0)) X1 X0
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) ≠ (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1))) ∨ (M.op (M.op X0 X0) (M.op X1 X1)) = (k (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) (M.op (M.op X1 X1) (M.op X2 X2))) X1
       have i₂ := eq21 (M.op (M.op X1 X1) (M.op X2 X2)) X1 X2 (M.op (M.op X1 X1) (M.op X2 X2))
       grind)
    | exact superpose eq21 eq11
    | (have j0 := eq11 (M.op (M.op X0 X0) (M.op X1 X1)) X1
       grind)
    | exact resolve eq11 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X2) X3) (M.op (M.op X0 X0) (M.op X1 X1))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1))) X2 X3
       have i₂ := eq21 (M.op (M.op X0 X0) (M.op X1 X1)) X0 X1 (M.op (M.op X0 X0) (M.op X1 X1))
       grind)
    | exact superpose eq21 eq22
    | exact resolve eq22 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (k (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq141 X0 X1 X2
       grind)
    | (have r₁ := eq141 X0 X0 X2
       have r₂ := eq64 (M.op X0 X0) (M.op X0 X0) (M.op X0 X0)
       grind)
    | (have r₁ := eq141 X0 X2 X2
       have r₂ := eq64 X0 (M.op (M.op X0 X0) (M.op X2 X2)) X2
       grind)
    | exact resolve eq141 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq151 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (k (M.op X1 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq146 X0 X1 X2
       have i₂ := eq143 X0 X1 X0 (M.op X1 X1)
       grind)
    | exact superpose eq143 eq146
    | exact resolve eq146 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq146
  have eq189 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 x X1 (M.op X1 X1)
       have i₂ := eq64 (M.op X1 X1) X0 x
       grind)
    | (have i₁ := eq22 (M.op X1 X1) X1 (M.op X1 X1)
       have i₂ := eq64 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq64 eq22
    | exact resolve eq22 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq323 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq44 x y
       grind)
    | exact superpose eq44 eq14
    | (have j1 := eq44 x x
       grind)
    | exact resolve eq14 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq337 : ∀ X0 X1 X2 X3 : G, (σ X0) = (M.op (M.op (σ X1) (M.op (M.op X2 X2) (M.op X3 X3))) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 (σ X1) X2 X3 (σ X0)
       have i₂ := eq44 X0 X1
       grind)
    | exact superpose eq44 eq21
    | (have j1 := eq44 X0 X1
       grind)
    | exact resolve eq21 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq353 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq44 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq456 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 X3)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq22 X3 x (M.op X0 (M.op X2 X2))
       have i₂ := eq71 X2 x X0
       grind)
    | exact superpose eq71 eq22
    | exact resolve eq22 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq71
  have eq990 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op (k (M.op X0 X0) X1) X2))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X2 (M.op X0 X0)
       have i₂ := eq151 X0 X0 X1
       grind)
    | exact superpose eq151 eq8
    | exact resolve eq8 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1008 : ∀ X0 X1 X2 X3 : G, (M.op (k (M.op X0 X0) X1) (M.op (M.op X2 X2) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq73 X3 X2 (M.op X0 X0)
       have i₂ := eq151 X0 X0 X1
       grind)
    | exact superpose eq151 eq73
    | exact resolve eq73 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq1012 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq189 X2 (M.op X0 X0)
       have i₂ := eq151 X0 X0 X1
       grind)
    | exact superpose eq151 eq189
    | exact resolve eq189 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq1132 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (k (σ (M.op X1 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1)
       have i₂ := eq1012 X1 (τ X2) X0
       grind)
    | exact superpose eq1012 eq16
    | exact resolve eq16 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1133 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) = (k (τ (M.op X1 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 (M.op X1 X1) X2
       have i₂ := eq1012 X1 (σ X2) X0
       grind)
    | exact superpose eq1012 eq20
    | exact resolve eq20 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012
  have eq3740 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1132 X0 x x
       have i₂ := eq1132 X1 x x
       grind)
    | exact superpose eq1132 eq1132
    | exact resolve eq1132 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132
  have eq4675 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1133 X0 x x
       have i₂ := eq1133 X1 x x
       grind)
    | exact superpose eq1133 eq1133
    | exact resolve eq1133 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133
  have eq4746 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq353 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq353
    | (have j0 := eq353 (τ X0)
       grind)
    | exact resolve eq353 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4752 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4746 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4746
    | (have j0 := eq4746 X0
       grind)
    | exact resolve eq4746 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4746
  have eq4766 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4752 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4752
    | (have j0 := eq4752 X0
       grind)
    | exact resolve eq4752 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4752
  have eq7982 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq323
       have i₂ := eq48 x X0 y
       grind)
    | exact superpose eq48 eq323
    | (have j1 := eq48 x X0 x
       grind)
    | exact resolve eq323 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq323
  have eq7985 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x X0) := by
    intro X0
    first
    | (have j0 := eq7982 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7982
  have eq18067 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) X0) ∨ x = (k x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ x) X1
       have i₂ := eq7985 X0
       grind)
    | exact superpose eq7985 eq11
    | (have j1 := eq7985 X1
       grind)
    | (have r₁ := eq11 (σ x) X1
       have r₂ := eq7985 X0
       grind)
    | exact resolve eq11 eq7985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7985
  have eq18199 : ∀ X0 X1 : G, (σ x) = (k (σ x) X0) ∨ x = (k x X1) := by
    intro X0 X1
    first
    | (have j0 := eq18067 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18067
  have eq26651 : ∀ X0 X1 : G, (τ (σ x)) = (k (τ (σ x)) X0) ∨ x = (k x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ x) X0
       have i₂ := eq18199 (σ X0) X1
       grind)
    | exact superpose eq18199 eq20
    | (have j1 := eq18199 X0 X1
       grind)
    | exact resolve eq20 eq18199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18199
  have eq26678 : ∀ X0 X1 : G, x = (k x X0) ∨ x = (k x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26651 X0 X1
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq26651
    | (have j0 := eq26651 X0 X0
       grind)
    | exact resolve eq26651 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26651
  have eq27153 : ∀ X0 : G, x ≠ x ∨ x = (k x X0) := by
    intro X0
    first
    | (have j0 := eq26678 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26678
  have eq27154 : ∀ X0 : G, x = (k x X0) := by
    intro X0
    first
    | (have j0 := eq27153 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27153
  have eq27581 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4766 x
       have i₂ := eq27154 x
       grind)
    | exact superpose eq27154 eq4766
    | (have j0 := eq4766 x
       grind)
    | (have r₁ := eq4766 x
       have r₂ := eq27154 x
       grind)
    | exact resolve eq4766 eq27154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27582 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq353 x
       have i₂ := eq27154 x
       grind)
    | exact superpose eq27154 eq353
    | (have j0 := eq353 x
       grind)
    | exact resolve eq353 eq27154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq27604 : ∀ X0 : G, (τ x) = (k (τ x) X0) := by
    intro X0
    first
    | (have i₁ := eq20 x X0
       have i₂ := eq27154 (σ X0)
       grind)
    | exact superpose eq27154 eq20
    | exact resolve eq20 eq27154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq27609 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq27582
  have eq27610 : x = (M.op x x) := by grind
  clear eq27581
  have eq27828 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq189 X0 x
       have i₂ := eq27610
       grind)
    | exact superpose eq27610 eq189
    | exact resolve eq189 eq27610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq27848 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq456 X0 X1 x
       have i₂ := eq27610
       grind)
    | exact superpose eq27610 eq456
    | exact resolve eq456 eq27610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq27887 : ∀ X0 : G, (σ x) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3740 X0 x
       have i₂ := eq27610
       grind)
    | exact superpose eq27610 eq3740
    | exact resolve eq3740 eq27610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3740
  have eq27890 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ x) := by
    intro X0
    first
    | (have i₁ := eq4675 X0 x
       have i₂ := eq27610
       grind)
    | exact superpose eq27610 eq4675
    | exact resolve eq4675 eq27610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4675 eq27610
  have eq29380 : ∀ X0 X1 X2 : G, (M.op (k (M.op X1 X1) X2) X0) = (M.op X0 x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq990 X1 X2 X0 (M.op (k (M.op X1 X1) X2) X0)
       have i₂ := eq27828 (M.op (k (M.op X1 X1) X2) X0)
       grind)
    | exact superpose eq27828 eq990
    | exact resolve eq990 eq27828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq29524 : ∀ X0 X2 : G, (M.op X0 x) = (M.op (k x X2) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq29380 X0 x X2
       have i₂ := eq27828 x
       grind)
    | exact superpose eq27828 eq29380
    | exact resolve eq29380 eq27828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29380
  have eq29689 : ∀ X0 : G, (M.op x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq29524 X0 x
       have i₂ := eq27154 x
       grind)
    | exact superpose eq27154 eq29524
    | exact resolve eq29524 eq27154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29524
  have eq31961 : (τ x) ≠ (τ x) ∨ (τ x) = (M.op (τ x) (τ x)) := by
    first
    | (have i₁ := eq4766 (τ x)
       have i₂ := eq27604 (τ x)
       grind)
    | exact superpose eq27604 eq4766
    | (have j0 := eq4766 (τ x)
       grind)
    | (have r₁ := eq4766 (τ x)
       have r₂ := eq27604 (τ x)
       grind)
    | exact resolve eq4766 eq27604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4766 eq27604
  have eq31991 : (τ x) = (M.op (τ x) (τ x)) := by grind
  clear eq31961
  have eq32013 : x = (τ x) := by
    first
    | (have i₁ := eq31991
       have i₂ := eq27828 (τ x)
       grind)
    | exact superpose eq27828 eq31991
    | exact resolve eq31991 eq27828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31991
  have eq34161 : x = (σ x) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq32013
       grind)
    | exact superpose eq32013 eq10
    | exact resolve eq10 eq32013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34163 : ∀ X0 : G, (k (σ X0) x) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq16 x X0
       have i₂ := eq32013
       grind)
    | exact superpose eq32013 eq16
    | exact resolve eq16 eq32013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq36156 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq34161
       grind)
    | exact superpose eq34161 eq14
    | exact resolve eq14 eq34161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34161
  have eq43371 : ∀ X0 X1 : G, (τ X0) = (τ x) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq27890 (M.op X0 X0)
       have i₂ := eq62 X0 X0 X0 X1
       grind)
    | exact superpose eq62 eq27890
    | (have j1 := eq62 X0 X1 x X1
       grind)
    | exact resolve eq27890 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq27890
  have eq43494 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (τ X0) = x := by
    intro X0 X1
    first
    | (have i₁ := eq43371 X0 X1
       have i₂ := eq32013
       grind)
    | exact superpose eq32013 eq43371
    | (have j0 := eq43371 X0 X1
       grind)
    | exact resolve eq43371 eq32013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32013 eq43371
  have eq47452 : ∀ X0 X1 X2 X3 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X1)) (M.op (M.op X2 X2) (M.op X3 X3))) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq337 (τ X0) (τ X1) X2 X3
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq337
    | (have j0 := eq337 (τ X0) X1 X2 X3
       grind)
    | exact resolve eq337 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq337
  have eq47960 : ∀ X0 X1 X2 X3 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X1)) (M.op (M.op X2 X2) (M.op X3 X3))) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq47452 X0 X1 X2 X3
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq47452
    | (have j0 := eq47452 X0 X1 X2 X3
       grind)
    | exact resolve eq47452 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47452
  have eq48399 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X1)) (M.op (M.op X2 X2) x)) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47960 X0 X1 X2 x
       have i₂ := eq27848 (M.op X2 X2) x
       grind)
    | exact superpose eq27848 eq47960
    | (have j0 := eq47960 X0 X1 X2 x
       grind)
    | exact resolve eq47960 eq27848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47960
  have eq48797 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X1)) (M.op x (M.op X2 X2))) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48399 X0 X1 X2
       have i₂ := eq29689 (M.op X2 X2)
       grind)
    | exact superpose eq29689 eq48399
    | (have j0 := eq48399 X0 X1 X2
       grind)
    | exact resolve eq48399 eq29689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48399
  have eq49168 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X1)) (M.op x x)) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq48797 X0 X1 x
       have i₂ := eq27848 x x
       grind)
    | exact superpose eq27848 eq48797
    | (have j0 := eq48797 X0 X1 x
       grind)
    | exact resolve eq48797 eq27848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48797
  have eq49507 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X1)) x) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq49168 X0 X1
       have i₂ := eq27848 (σ (τ X1)) x
       grind)
    | exact superpose eq27848 eq49168
    | (have j0 := eq49168 X0 X1
       grind)
    | exact resolve eq49168 eq27848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27848 eq49168
  have eq49761 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op x (σ (τ X1))) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq49507 X0 X1
       have i₂ := eq29689 (σ (τ X1))
       grind)
    | exact superpose eq29689 eq49507
    | (have j0 := eq49507 X0 X1
       grind)
    | exact resolve eq49507 eq29689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49507
  have eq49951 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op x X1) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq49761 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq49761
    | (have j0 := eq49761 X0 X1
       grind)
    | exact resolve eq49761 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49761
  have eq50063 : ∀ X0 X1 : G, (M.op (M.op x X1) (k X0 X1)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq49951 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq49951
    | (have j0 := eq49951 X0 X1
       grind)
    | exact resolve eq49951 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49951
  have eq50122 : ∀ X0 X1 : G, (σ (τ X0)) = x ∨ (M.op (M.op x X1) (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq50063 X0 X1
       have i₂ := eq27828 (σ (τ X0))
       grind)
    | exact superpose eq27828 eq50063
    | (have j0 := eq50063 X0 X1
       grind)
    | exact resolve eq50063 eq27828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50063
  have eq50156 : ∀ X0 X1 : G, (M.op (M.op x X1) (k X0 X1)) = X0 ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq50122 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq50122
    | (have j0 := eq50122 X0 X1
       grind)
    | exact resolve eq50122 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50122
  have eq186064 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) x) ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq34163 X0
       have i₂ := eq43494 (σ X0) x
       grind)
    | exact superpose eq43494 eq34163
    | (have j1 := eq43494 (σ X0) x
       grind)
    | exact resolve eq34163 eq43494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34163 eq43494
  have eq186118 : ∀ X0 : G, (σ (k X0 x)) = (M.op x (σ X0)) ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq186064 X0
       have i₂ := eq29689 (σ X0)
       grind)
    | exact superpose eq29689 eq186064
    | (have j0 := eq186064 X0
       grind)
    | exact resolve eq186064 eq29689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29689 eq186064
  have eq186226 : ∀ X0 : G, (σ (k X0 x)) = (M.op x (σ X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq186118 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq186118
    | (have j0 := eq186118 X0
       grind)
    | exact resolve eq186118 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186118
  have eq223626 : ∀ X0 X1 X2 : G, (M.op (k (M.op X1 X1) X2) X0) = (k X0 x) ∨ x = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1008 X1 X2 x (k X0 x)
       have i₂ := eq50156 X0 x
       grind)
    | exact superpose eq50156 eq1008
    | (have j1 := eq50156 X0 X1
       grind)
    | exact resolve eq1008 eq50156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008 eq50156
  have eq223718 : ∀ X0 X2 : G, (M.op (k x X2) X0) = (k X0 x) ∨ x = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq223626 X0 x X2
       have i₂ := eq27828 x
       grind)
    | exact superpose eq27828 eq223626
    | (have j0 := eq223626 X0 x X2
       grind)
    | exact resolve eq223626 eq27828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27828 eq223626
  have eq223819 : ∀ X0 : G, (M.op x X0) = (k X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq223718 X0 x
       have i₂ := eq27154 x
       grind)
    | exact superpose eq27154 eq223718
    | (have j0 := eq223718 X0 x
       grind)
    | exact resolve eq223718 eq27154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27154 eq223718
  have eq361297 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) ∨ x = X0 ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq186226 X0
       have i₂ := eq223819 X0
       grind)
    | exact superpose eq223819 eq186226
    | (have j0 := eq186226 X0
       have j1 := eq223819 X0
       grind)
    | exact resolve eq186226 eq223819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186226 eq223819
  have eq361379 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq361297 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361297
  have eq372140 : (M.op x (σ y)) ≠ (M.op x (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq36156
       have i₂ := eq361379 y
       grind)
    | exact superpose eq361379 eq36156
    | (have j1 := eq361379 y
       grind)
    | (have r₁ := eq36156
       have r₂ := eq361379 y
       grind)
    | exact resolve eq36156 eq361379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36156 eq361379
  have eq372158 : x = y := by grind
  clear eq372140
  have eq373046 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq372158
       grind)
    | exact superpose eq372158 eq14
    | exact resolve eq14 eq372158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372158
  have eq373047 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq373046
       have i₂ := eq27887 x
       grind)
    | exact superpose eq27887 eq373046
    | exact resolve eq373046 eq27887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27887 eq373046
  have eq373049 : False := by grind
  exact eq373049

/-- `Equation695`: `x = y ◇ (x ◇ ((z ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_y_pxy_Equation695 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law695 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law695.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X2 X2) X1))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
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
  have eq17 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2))) (M.op X3 X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2))) X2
       have i₂ := eq8 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op (M.op X1 X1) X2) X0
       have i₂ := eq8 (M.op X0 X0) X2 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq25 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X1 ∨ (k X0 X2) = (M.op X0 X2) := by
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
  have eq28 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq30 : ∀ X0 X1 X2 : G, (k X0 X1) = X1 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq25 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq42 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X2 (M.op X0 X0) (M.op X1 X1)
       have i₂ := eq18 X1 X0 (M.op X0 X0)
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (M.op X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X1 X1) (M.op X0 X0)
       have i₂ := eq18 X1 X0 (M.op X0 X0)
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X1 X1) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (M.op X2 X2) (M.op (M.op X1 X1) X0)) (M.op (M.op X1 X1) X0) X2
       have i₂ := eq18 (M.op (M.op X2 X2) (M.op (M.op X1 X1) X0)) X1 X0
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22
    | exact resolve eq22 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (k X1 X2) = (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq30 X1 (σ X0) X2
       grind)
    | exact superpose eq30 eq22
    | (have j1 := eq30 X1 X1 X2
       grind)
    | exact resolve eq22 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq79 : ∀ X0 X1 X2 : G, (k (τ X1) X0) = X0 ∨ (k X1 X2) = (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq73 X0 X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq73
    | (have j0 := eq73 X0 X1 X2
       grind)
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq102 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X3 X1)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq17 X1 (M.op X0 X0) x X3
       have i₂ := eq18 x X0 (M.op X0 X0)
       grind)
    | exact superpose eq18 eq17
    | exact resolve eq17 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op (M.op X4 X4) (M.op X5 X5))) = (M.op (M.op (M.op X0 X1) (M.op (M.op X2 X2) (M.op X3 X3))) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq17 (M.op X0 X1) X2 X3 (M.op X1 (M.op (M.op X4 X4) (M.op X5 X5)))
       have i₂ := eq17 X1 X4 X5 X0
       grind)
    | exact superpose eq17 eq17
    | exact resolve eq17 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq14
    | (have j1 := eq28 x x
       grind)
    | exact resolve eq14 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) X1
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq11
    | (have j0 := eq11 (σ X0) X1
       have j1 := eq28 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq11 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 X1 X2 X3 : G, (σ X0) = (M.op (M.op (σ X1) (M.op (M.op X2 X2) (M.op X3 X3))) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17 (σ X1) X2 X3 (σ X0)
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq17
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq17 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq217 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq28 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq197 X0 X1
       have j1 := eq11 (σ X0) X1
       grind)
    | (have r₁ := eq197 X0 X1
       have r₂ := eq11 (σ X0) X1
       grind)
    | exact resolve eq197 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq466 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 x X1 (M.op X1 X1)
       have i₂ := eq42 (M.op X1 X1) X0 x
       grind)
    | (have i₁ := eq18 (M.op X1 X1) X1 (M.op X1 X1)
       have i₂ := eq42 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq42 eq18
    | exact resolve eq18 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq587 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (M.op X2 X2) X1) X1 X2
       have i₂ := eq466 (M.op (M.op X2 X2) X1) X0
       grind)
    | (have i₁ := eq8 (M.op (M.op X2 X2) X1) X1 X2
       have i₂ := eq466 X0 (M.op (M.op X2 X2) X1)
       grind)
    | exact superpose eq466 eq8
    | exact resolve eq8 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq648 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 X3)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq18 X3 x (M.op X0 (M.op X2 X2))
       have i₂ := eq49 X2 x X0
       grind)
    | exact superpose eq49 eq18
    | exact resolve eq18 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq49
  have eq929 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op (M.op X1 X1) X0) x
       have i₂ := eq51 X0 X1 x
       grind)
    | exact superpose eq51 eq8
    | exact resolve eq8 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1040 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq102 X2 X1 X1
       have i₂ := eq466 X1 X0
       grind)
    | (have i₁ := eq102 X2 X1 X1
       have i₂ := eq466 X0 X1
       grind)
    | exact superpose eq466 eq102
    | exact resolve eq102 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq1283 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k (σ (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq221 (τ X0) X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq221
    | (have j0 := eq221 (τ X0) X1
       grind)
    | exact resolve eq221 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq1294 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k (σ (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1283 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1283
    | (have j0 := eq1283 X0 X1
       grind)
    | exact resolve eq1283 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283
  have eq1301 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1294 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1294
    | (have j0 := eq1294 X0 X1
       grind)
    | exact resolve eq1294 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294
  have eq1318 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1301 (τ X0) X1
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq1301
    | (have j0 := eq1301 (τ X0) X1
       grind)
    | exact resolve eq1301 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1301
  have eq4601 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq217 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq217
    | (have j0 := eq217 (τ X0)
       grind)
    | exact resolve eq217 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq4617 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4601 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4601
    | (have j0 := eq4601 X0
       grind)
    | exact resolve eq4601 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4601
  have eq4627 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4617 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4617
    | (have j0 := eq4617 X0
       grind)
    | exact resolve eq4617 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4617
  have eq7584 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq195
       have i₂ := eq30 x X0 y
       grind)
    | exact superpose eq30 eq195
    | (have j1 := eq30 x X0 x
       grind)
    | exact resolve eq195 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq195
  have eq7587 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7584 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7584
  have eq7694 : ∀ X0 : G, (σ (τ X0)) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x
       have i₂ := eq7587 (τ X0)
       grind)
    | exact superpose eq7587 eq16
    | exact resolve eq16 eq7587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7587
  have eq7698 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq7694 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7694
    | exact resolve eq7694 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7694
  have eq7713 : ∀ X0 : G, (k (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7698 X0
       have j1 := eq11 (σ x) X0
       grind)
    | (have r₁ := eq7698 X0
       have r₂ := eq11 (σ x) x
       grind)
    | exact resolve eq7698 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7698
  have eq7923 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k (τ (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1318 (σ x) X0
       have i₂ := eq7713 (σ x)
       grind)
    | exact superpose eq7713 eq1318
    | (have j0 := eq1318 (σ x) X0
       grind)
    | exact resolve eq1318 eq7713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7925 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4627 (σ x)
       have i₂ := eq7713 (σ x)
       grind)
    | exact superpose eq7713 eq4627
    | (have j0 := eq4627 (σ x)
       grind)
    | (have r₁ := eq4627 (σ x)
       have r₂ := eq7713 (σ x)
       grind)
    | exact resolve eq4627 eq7713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7713
  have eq7942 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq7925
  have eq7943 : ∀ X0 : G, (k (τ (σ x)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7923 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7923
  have eq7952 : ∀ X0 : G, (k x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7943 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq7943
    | exact resolve eq7943 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7943
  have eq8679 : ∀ X0 : G, (τ x) ≠ (τ x) ∨ (k (τ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1318 x X0
       have i₂ := eq7952 x
       grind)
    | exact superpose eq7952 eq1318
    | (have j0 := eq1318 x X0
       grind)
    | exact resolve eq1318 eq7952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318
  have eq8681 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4627 x
       have i₂ := eq7952 x
       grind)
    | exact superpose eq7952 eq4627
    | (have j0 := eq4627 x
       grind)
    | (have r₁ := eq4627 x
       have r₂ := eq7952 x
       grind)
    | exact resolve eq4627 eq7952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7952
  have eq8698 : x = (M.op x x) := by grind
  clear eq8681
  have eq8699 : ∀ X0 : G, (k (τ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq8679 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8679
  have eq9177 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op x X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 x
       have i₂ := eq8698
       grind)
    | exact superpose eq8698 eq8
    | exact resolve eq8 eq8698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9198 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op x X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 x X0
       have i₂ := eq8698
       grind)
    | exact superpose eq8698 eq51
    | exact resolve eq51 eq8698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq9231 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq466 X0 x
       have i₂ := eq8698
       grind)
    | exact superpose eq8698 eq466
    | exact resolve eq466 eq8698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq9234 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq587 x X1 X0
       have i₂ := eq8698
       grind)
    | exact superpose eq8698 eq587
    | exact resolve eq587 eq8698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq9237 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq648 X0 X1 x
       have i₂ := eq8698
       grind)
    | exact superpose eq8698 eq648
    | exact resolve eq648 eq8698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq9242 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1040 x X0 X1
       have i₂ := eq8698
       grind)
    | exact superpose eq8698 eq1040
    | exact resolve eq1040 eq8698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040 eq8698
  have eq9279 : ∀ X1 : G, (M.op (M.op x X1) x) = X1 := by
    intro X1
    first
    | (have i₁ := eq9198 x X1
       have i₂ := eq9234 x (M.op x X1)
       grind)
    | exact superpose eq9234 eq9198
    | exact resolve eq9198 eq9234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9198
  have eq9887 : ∀ X0 : G, x = (σ (k X0 X0)) ∨ (σ X0) = x := by
    intro X0
    first
    | (have i₁ := eq28 X0 X0
       have i₂ := eq9231 (σ X0)
       grind)
    | exact superpose eq9231 eq28
    | exact resolve eq28 eq9231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq10816 : (τ x) ≠ (τ x) ∨ (τ x) = (M.op (τ x) (τ x)) := by
    first
    | (have i₁ := eq4627 (τ x)
       have i₂ := eq8699 (τ x)
       grind)
    | exact superpose eq8699 eq4627
    | (have j0 := eq4627 (τ x)
       grind)
    | (have r₁ := eq4627 (τ x)
       have r₂ := eq8699 (τ x)
       grind)
    | exact resolve eq4627 eq8699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4627 eq8699
  have eq10834 : (τ x) = (M.op (τ x) (τ x)) := by grind
  clear eq10816
  have eq10852 : x = (τ x) := by
    first
    | (have i₁ := eq10834
       have i₂ := eq9231 (τ x)
       grind)
    | exact superpose eq9231 eq10834
    | exact resolve eq10834 eq9231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10834
  have eq11747 : x = (σ x) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq10852
       grind)
    | exact superpose eq10852 eq10
    | exact resolve eq10 eq10852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11749 : ∀ X0 : G, (k (σ X0) x) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq16 x X0
       have i₂ := eq10852
       grind)
    | exact superpose eq10852 eq16
    | exact resolve eq16 eq10852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq10852
  have eq12601 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq11747
       grind)
    | exact superpose eq11747 eq14
    | exact resolve eq14 eq11747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11747
  have eq18263 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op (M.op X1 X1) x) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq929 x X1 (M.op x X0)
       have i₂ := eq9279 X0
       grind)
    | exact superpose eq9279 eq929
    | exact resolve eq929 eq9279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929
  have eq18264 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq18263 X0 x
       have i₂ := eq9234 x x
       grind)
    | exact superpose eq9234 eq18263
    | exact resolve eq18263 eq9234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18263
  have eq18299 : ∀ X0 : G, (M.op x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq18264 X0
       have i₂ := eq9234 x X0
       grind)
    | exact superpose eq9234 eq18264
    | exact resolve eq18264 eq9234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18264
  have eq20618 : ∀ X0 : G, (M.op x (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9279 X0
       have i₂ := eq18299 (M.op x X0)
       grind)
    | exact superpose eq18299 eq9279
    | exact resolve eq9279 eq18299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9279
  have eq29011 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X3 (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2)))) = (M.op (M.op (M.op (M.op X4 X4) X3) X0) (M.op (M.op X5 X5) (M.op X6 X6))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq8 (M.op (M.op (M.op (M.op X4 X4) X3) X0) (M.op (M.op X5 X5) (M.op X6 X6))) X3 X4
       have i₂ := eq113 (M.op (M.op X4 X4) X3) X0 X5 X6 X1 X2
       grind)
    | exact superpose eq113 eq8
    | exact resolve eq8 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29040 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2)))) = (M.op (M.op (M.op (M.op X4 X4) X3) X0) (M.op (M.op X5 X5) x)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq29011 X0 X1 X2 X3 X4 X5 x
       have i₂ := eq9237 (M.op X5 X5) x
       grind)
    | exact superpose eq9237 eq29011
    | exact resolve eq29011 eq9237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29011
  have eq29686 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2)))) = (M.op (M.op (M.op (M.op X4 X4) X3) X0) (M.op x (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq29040 X0 X1 X2 X3 X4 X5
       have i₂ := eq18299 (M.op X5 X5)
       grind)
    | exact superpose eq18299 eq29040
    | exact resolve eq29040 eq18299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29040
  have eq30153 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2)))) = (M.op (M.op (M.op (M.op X4 X4) X3) X0) (M.op x x)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq29686 X0 X1 X2 X3 X4 x
       have i₂ := eq9237 x x
       grind)
    | exact superpose eq9237 eq29686
    | exact resolve eq29686 eq9237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29686
  have eq30593 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2)))) = (M.op (M.op (M.op (M.op X4 X4) X3) X0) x) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq30153 X0 X1 X2 X3 X4
       have i₂ := eq9237 (M.op (M.op (M.op X4 X4) X3) X0) x
       grind)
    | exact superpose eq9237 eq30153
    | exact resolve eq30153 eq9237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30153
  have eq31020 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2)))) = (M.op x (M.op (M.op (M.op X4 X4) X3) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq30593 X0 X1 X2 X3 X4
       have i₂ := eq18299 (M.op (M.op (M.op X4 X4) X3) X0)
       grind)
    | exact superpose eq18299 eq30593
    | exact resolve eq30593 eq18299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30593
  have eq31373 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2)))) = (M.op x (M.op (M.op X3 x) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq31020 X0 X1 X2 X3 x
       have i₂ := eq9234 x X3
       grind)
    | exact superpose eq9234 eq31020
    | exact resolve eq31020 eq9234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9234 eq31020
  have eq31663 : ∀ X0 X1 X3 : G, (M.op X3 (M.op X0 (M.op (M.op X1 X1) x))) = (M.op x (M.op (M.op X3 x) X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq31373 X0 X1 x X3
       have i₂ := eq9237 (M.op X1 X1) x
       grind)
    | exact superpose eq9237 eq31373
    | exact resolve eq31373 eq9237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31373
  have eq31899 : ∀ X0 X1 X3 : G, (M.op X3 (M.op X0 (M.op x (M.op X1 X1)))) = (M.op x (M.op (M.op X3 x) X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq31663 X0 X1 X3
       have i₂ := eq18299 (M.op X1 X1)
       grind)
    | exact superpose eq18299 eq31663
    | exact resolve eq31663 eq18299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31663
  have eq32057 : ∀ X0 X3 : G, (M.op X3 (M.op X0 (M.op x x))) = (M.op x (M.op (M.op X3 x) X0)) := by
    intro X0 X3
    first
    | (have i₁ := eq31899 X0 x X3
       have i₂ := eq9237 x x
       grind)
    | exact superpose eq9237 eq31899
    | exact resolve eq31899 eq9237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31899
  have eq32172 : ∀ X0 X3 : G, (M.op X3 (M.op X0 x)) = (M.op x (M.op (M.op X3 x) X0)) := by
    intro X0 X3
    first
    | (have i₁ := eq32057 X0 X3
       have i₂ := eq9237 X0 x
       grind)
    | exact superpose eq9237 eq32057
    | exact resolve eq32057 eq9237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32057
  have eq51762 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op (M.op X2 X2) (M.op X3 X3))) X0) x) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9242 X1 (M.op x x)
       have i₂ := eq113 X0 X1 X2 X3 x x
       grind)
    | exact superpose eq113 eq9242
    | exact resolve eq9242 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq9242
  have eq51985 : ∀ X0 X1 X2 X3 : G, (M.op x (M.op (M.op (M.op X0 X1) (M.op (M.op X2 X2) (M.op X3 X3))) X0)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51762 X0 X1 X2 X3
       have i₂ := eq18299 (M.op (M.op (M.op X0 X1) (M.op (M.op X2 X2) (M.op X3 X3))) X0)
       grind)
    | exact superpose eq18299 eq51762
    | exact resolve eq51762 eq18299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51762
  have eq52084 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op (M.op X0 X1) (M.op (M.op X2 X2) x)) X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51985 X0 X1 X2 x
       have i₂ := eq9237 (M.op X2 X2) x
       grind)
    | exact superpose eq9237 eq51985
    | exact resolve eq51985 eq9237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51985
  have eq52144 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op (M.op X0 X1) (M.op x (M.op X2 X2))) X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52084 X0 X1 X2
       have i₂ := eq18299 (M.op X2 X2)
       grind)
    | exact superpose eq18299 eq52084
    | exact resolve eq52084 eq18299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52084
  have eq52153 : ∀ X0 X1 : G, (M.op x (M.op (M.op (M.op X0 X1) (M.op x x)) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52144 X0 X1 x
       have i₂ := eq9237 x x
       grind)
    | exact superpose eq9237 eq52144
    | exact resolve eq52144 eq9237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52144
  have eq52158 : ∀ X0 X1 : G, (M.op x (M.op (M.op (M.op X0 X1) x) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52153 X0 X1
       have i₂ := eq9237 (M.op X0 X1) x
       grind)
    | exact superpose eq9237 eq52153
    | exact resolve eq52153 eq9237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52153
  have eq52163 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52158 X0 X1
       have i₂ := eq32172 X0 (M.op X0 X1)
       grind)
    | exact superpose eq32172 eq52158
    | exact resolve eq52158 eq32172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52158
  have eq64132 : ∀ X0 X1 X2 X3 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X1)) (M.op (M.op X2 X2) (M.op X3 X3))) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq206 (τ X0) (τ X1) X2 X3
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq206
    | (have j0 := eq206 (τ X0) X1 X2 X3
       grind)
    | exact resolve eq206 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq206
  have eq64578 : ∀ X0 X1 X2 X3 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X1)) (M.op (M.op X2 X2) (M.op X3 X3))) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64132 X0 X1 X2 X3
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq64132
    | (have j0 := eq64132 X0 X1 X2 X3
       grind)
    | exact resolve eq64132 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64132
  have eq65012 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X1)) (M.op (M.op X2 X2) x)) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64578 X0 X1 X2 x
       have i₂ := eq9237 (M.op X2 X2) x
       grind)
    | exact superpose eq9237 eq64578
    | (have j0 := eq64578 X0 X1 X2 x
       grind)
    | exact resolve eq64578 eq9237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64578
  have eq65408 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X1)) (M.op x (M.op X2 X2))) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65012 X0 X1 X2
       have i₂ := eq18299 (M.op X2 X2)
       grind)
    | exact superpose eq18299 eq65012
    | (have j0 := eq65012 X0 X1 X2
       grind)
    | exact resolve eq65012 eq18299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65012
  have eq65761 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X1)) (M.op x x)) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq65408 X0 X1 x
       have i₂ := eq9237 x x
       grind)
    | exact superpose eq9237 eq65408
    | (have j0 := eq65408 X0 X1 x
       grind)
    | exact resolve eq65408 eq9237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65408
  have eq66071 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X1)) x) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq65761 X0 X1
       have i₂ := eq9237 (σ (τ X1)) x
       grind)
    | exact superpose eq9237 eq65761
    | (have j0 := eq65761 X0 X1
       grind)
    | exact resolve eq65761 eq9237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9237 eq65761
  have eq66304 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op x (σ (τ X1))) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq66071 X0 X1
       have i₂ := eq18299 (σ (τ X1))
       grind)
    | exact superpose eq18299 eq66071
    | (have j0 := eq66071 X0 X1
       grind)
    | exact resolve eq66071 eq18299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66071
  have eq66468 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op x X1) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq66304 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq66304
    | (have j0 := eq66304 X0 X1
       grind)
    | exact resolve eq66304 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66304
  have eq66563 : ∀ X0 X1 : G, (M.op (M.op x X1) (k X0 X1)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq66468 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq66468
    | (have j0 := eq66468 X0 X1
       grind)
    | exact resolve eq66468 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66468
  have eq66626 : ∀ X0 X1 : G, (σ (τ X0)) = x ∨ (M.op (M.op x X1) (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq66563 X0 X1
       have i₂ := eq9231 (σ (τ X0))
       grind)
    | exact superpose eq9231 eq66563
    | (have j0 := eq66563 X0 X1
       grind)
    | exact resolve eq66563 eq9231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66563
  have eq66664 : ∀ X0 X1 : G, (M.op (M.op x X1) (k X0 X1)) = X0 ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq66626 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq66626
    | (have j0 := eq66626 X0 X1
       grind)
    | exact resolve eq66626 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66626
  have eq72006 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op X0 (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq52163 X1 (M.op X0 (M.op x X1))
       have i₂ := eq9177 X1 X0
       grind)
    | exact superpose eq9177 eq52163
    | exact resolve eq52163 eq9177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9177 eq52163
  have eq95716 : ∀ X0 : G, x = (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq15 X0 (τ X0)
       have i₂ := eq9887 (τ X0)
       grind)
    | exact superpose eq9887 eq15
    | (have j1 := eq9887 (τ X0)
       grind)
    | exact resolve eq15 eq9887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq9887
  have eq95849 : ∀ X0 : G, x = (k X0 X0) ∨ (σ (τ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq95716 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq95716
    | (have j0 := eq95716 X0
       grind)
    | exact resolve eq95716 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95716
  have eq95931 : ∀ X0 : G, x = (k X0 X0) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq95849 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq95849
    | (have j0 := eq95849 X0
       grind)
    | exact resolve eq95849 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95849
  have eq97407 : ∀ X0 X1 : G, (τ X0) = x ∨ (k X0 X1) = (M.op X0 X1) ∨ (τ X0) = x := by
    intro X0 X1
    first
    | (have i₁ := eq79 (τ X0) X0 X1
       have i₂ := eq95931 (τ X0)
       grind)
    | exact superpose eq95931 eq79
    | (have j0 := eq79 X0 X0 X1
       have j1 := eq95931 (τ X0)
       grind)
    | exact resolve eq79 eq95931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq95931
  have eq97428 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (τ X0) = x := by
    intro X0 X1
    first
    | (have j0 := eq97407 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97407
  have eq158181 : ∀ X0 : G, (M.op (σ X0) x) = (σ (k X0 x)) ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq11749 X0
       have i₂ := eq97428 (σ X0) x
       grind)
    | exact superpose eq97428 eq11749
    | (have j1 := eq97428 (σ X0) x
       grind)
    | exact resolve eq11749 eq97428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11749 eq97428
  have eq158271 : ∀ X0 : G, (σ (k X0 x)) = (M.op x (σ X0)) ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq158181 X0
       have i₂ := eq18299 (σ X0)
       grind)
    | exact superpose eq18299 eq158181
    | (have j0 := eq158181 X0
       grind)
    | exact resolve eq158181 eq18299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18299 eq158181
  have eq158374 : ∀ X0 : G, (σ (k X0 x)) = (M.op x (σ X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq158271 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq158271
    | (have j0 := eq158271 X0
       grind)
    | exact resolve eq158271 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158271
  have eq187773 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op (k X0 x) x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq32172 (k X0 x) x
       have i₂ := eq66664 X0 x
       grind)
    | exact superpose eq66664 eq32172
    | (have j1 := eq66664 X0 x
       grind)
    | exact resolve eq32172 eq66664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32172 eq66664
  have eq187861 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op x (k X0 x))) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq187773 X0
       have i₂ := eq72006 x (k X0 x)
       grind)
    | exact superpose eq72006 eq187773
    | (have j0 := eq187773 X0
       grind)
    | exact resolve eq187773 eq72006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72006 eq187773
  have eq187967 : ∀ X0 : G, (M.op x X0) = (k X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq187861 X0
       have i₂ := eq20618 (k X0 x)
       grind)
    | exact superpose eq20618 eq187861
    | (have j0 := eq187861 X0
       grind)
    | exact resolve eq187861 eq20618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20618 eq187861
  have eq342342 : ∀ X0 : G, (σ (M.op x X0)) = (M.op x (σ X0)) ∨ x = X0 ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq158374 X0
       have i₂ := eq187967 X0
       grind)
    | exact superpose eq187967 eq158374
    | (have j0 := eq158374 X0
       have j1 := eq187967 X0
       grind)
    | exact resolve eq158374 eq187967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158374 eq187967
  have eq342552 : ∀ X0 : G, (σ (M.op x X0)) = (M.op x (σ X0)) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq342342 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342342
  have eq373228 : (M.op x (σ y)) ≠ (M.op x (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq12601
       have i₂ := eq342552 y
       grind)
    | exact superpose eq342552 eq12601
    | (have j1 := eq342552 y
       grind)
    | (have r₁ := eq12601
       have r₂ := eq342552 y
       grind)
    | exact resolve eq12601 eq342552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12601 eq342552
  have eq373344 : x = y := by grind
  clear eq373228
  have eq376562 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq373344
       grind)
    | exact superpose eq373344 eq14
    | exact resolve eq14 eq373344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373344
  have eq376563 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq376562
       have i₂ := eq9231 x
       grind)
    | exact superpose eq9231 eq376562
    | exact resolve eq376562 eq9231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9231 eq376562
  have eq376565 : False := by grind
  exact eq376565
