import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3735`: `x ◇ y = (x ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pyy_pyx_Equation3735 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3735 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3735.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X0)) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X0 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X0 X2) X3 (M.op X1 X0)
       have i₂ := eq8 X0 X1 X2
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
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X1 X1)
       have i₂ := eq8 X1 X1 X1
       grind)
    | exact superpose eq8 eq11
    | (have r₁ := eq11 X0 (M.op X1 X1)
       have r₂ := eq8 X1 X1 X1
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq34 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (M.op X0 X0)
       have i₂ := eq32 X0 (τ X1)
       grind)
    | exact superpose eq32 eq15
    | exact resolve eq15 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
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
  have eq41 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 X0 (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 X0 X0
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq40 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq46 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq66 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq45 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq45 eq13
    | (have j1 := eq45 (σ X0) X2 X2
       grind)
    | exact resolve eq13 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq45 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 X2 : G, (τ X0) = (k X1 (τ X0)) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq45 X0 (σ X1) X2
       grind)
    | exact superpose eq45 eq28
    | (have j1 := eq45 (τ X0) X1 X2
       grind)
    | exact resolve eq28 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = (M.op (M.op X1 X3) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X1 X3 X0 (M.op X0 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq21
    | exact resolve eq21 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq117 X0 X1 X2 x
       have i₂ := eq8 X1 X0 x
       grind)
    | exact superpose eq8 eq117
    | exact resolve eq117 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq287 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq130 (M.op X0 X2) (M.op X1 X0) X2
       have i₂ := eq130 X0 X1 X2
       grind)
    | exact superpose eq130 eq130
    | exact resolve eq130 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X0 X1 X2 X1
       have i₂ := eq130 X1 X0 (M.op X0 X2)
       grind)
    | exact superpose eq130 eq21
    | exact resolve eq21 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq130
  have eq339 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq287 X0 X1 X2 X3
       have i₂ := eq306 X0 (M.op (M.op X1 X2) X3) X1
       grind)
    | exact superpose eq306 eq287
    | exact resolve eq287 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq345 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq339 X0 X1 x X3
       have i₂ := eq306 X1 X3 x
       grind)
    | exact superpose eq306 eq339
    | exact resolve eq339 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq359 : ∀ X0 X1 X2 : G, (M.op (σ X1) X2) = (M.op (σ (k X0 X1)) (M.op X2 (σ X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (σ X1) X2 (σ X0)
       have i₂ := eq41 X1 X0
       grind)
    | exact superpose eq41 eq8
    | (have j1 := eq41 X1 X1
       grind)
    | exact resolve eq8 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 X1 : G, (σ (k X0 X0)) = (k X1 (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 (σ X1) X1
       have i₂ := eq41 X1 X1
       grind)
    | exact superpose eq41 eq32
    | (have j1 := eq41 X0 X1
       grind)
    | exact resolve eq32 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq390 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq41 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq406 : ∀ X0 X1 X2 : G, (M.op (σ X1) X2) = (M.op (σ (k X0 X1)) X2) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq359 X0 X1 X2
       have i₂ := eq345 (σ (k X0 X1)) X2 (σ X1)
       grind)
    | exact superpose eq345 eq359
    | (have j0 := eq359 X0 X1 X2
       grind)
    | exact resolve eq359 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq448 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (k X1 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X1 (M.op X0 X2)
       have i₂ := eq306 X0 X1 X2
       grind)
    | exact superpose eq306 eq71
    | (have j0 := eq71 X1 (M.op X0 X2)
       grind)
    | (have r₁ := eq71 X1 (M.op X0 X1)
       have r₂ := eq306 X0 X1 X1
       grind)
    | exact resolve eq71 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq454 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 (M.op X0 X1)) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 (M.op X0 X2)
       have i₂ := eq306 X0 (M.op X0 X2) X2
       grind)
    | exact superpose eq306 eq11
    | exact resolve eq11 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 (M.op X0 X1)) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq454 X0 X1 X2
       have i₂ := eq345 X0 X0 X1
       grind)
    | exact superpose eq345 eq454
    | (have j0 := eq454 X0 X1 X2
       grind)
    | (have r₁ := eq454 x x X2
       have r₂ := eq345 x x x
       grind)
    | exact resolve eq454 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq478 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq459 X0 X1 X2
       have i₂ := eq345 X0 X0 X1
       grind)
    | exact superpose eq345 eq459
    | (have j0 := eq459 X0 X1 X2
       grind)
    | (have r₁ := eq459 (M.op X1 x) X1 X2
       have r₂ := eq345 (M.op X1 x) X1 x
       grind)
    | (have r₁ := eq459 X1 (M.op X1 x) X2
       have r₂ := eq345 X1 X1 x
       grind)
    | exact resolve eq459 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq1685 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (M.op (σ X0) X2) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80 (σ X0) X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq80
    | (have j0 := eq80 (σ X0) X1 X2
       grind)
    | exact resolve eq80 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq1778 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq42
    | (have j0 := eq42 X1 X1
       grind)
    | exact resolve eq42 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq1881 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1778 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1778
    | (have j0 := eq1778 X0 X1
       grind)
    | exact resolve eq1778 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1778
  have eq2725 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X1 X1
       have i₂ := eq1881 X0 X1
       grind)
    | exact superpose eq1881 eq34
    | (have j1 := eq1881 X2 X0
       grind)
    | exact resolve eq34 eq1881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1881
  have eq3568 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq390 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq390
    | (have j0 := eq390 (τ X0)
       grind)
    | exact resolve eq390 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq3587 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3568 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3568
    | (have j0 := eq3568 X0
       grind)
    | exact resolve eq3568 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3568
  have eq3597 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3587 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3587
    | (have j0 := eq3587 X0
       grind)
    | exact resolve eq3587 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3587
  have eq4224 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq66 x y X0
       grind)
    | exact superpose eq66 eq14
    | (have j1 := eq66 x x X0
       grind)
    | exact resolve eq14 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq4326 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq4224 X0
       have j1 := eq2725 x X0 x
       grind)
    | (have r₁ := eq4224 X0
       have r₂ := eq2725 x x y
       grind)
    | exact resolve eq4224 eq2725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725 eq4224
  have eq4374 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3597 (σ x)
       have i₂ := eq4326 (σ x)
       grind)
    | exact superpose eq4326 eq3597
    | (have j0 := eq3597 (σ x)
       grind)
    | (have r₁ := eq3597 (σ x)
       have r₂ := eq4326 (σ x)
       grind)
    | exact resolve eq3597 eq4326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4391 : ∀ X0 : G, (τ (σ x)) = (k X0 (τ (σ x))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (σ x)
       have i₂ := eq4326 (σ X0)
       grind)
    | exact superpose eq4326 eq28
    | exact resolve eq28 eq4326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4326
  have eq4396 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4374
  have eq4397 : ∀ X0 : G, x = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq4391 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq4391
    | exact resolve eq4391 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4391
  have eq4538 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3597 x
       have i₂ := eq4397 x
       grind)
    | exact superpose eq4397 eq3597
    | (have j0 := eq3597 x
       grind)
    | (have r₁ := eq3597 x
       have r₂ := eq4397 x
       grind)
    | exact resolve eq3597 eq4397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4397
  have eq4557 : x = (M.op x x) := by grind
  clear eq4538
  have eq9381 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = (k X1 (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq373 (τ X0) X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq373
    | (have j0 := eq373 (τ X0) X1
       grind)
    | exact resolve eq373 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq373
  have eq9449 : ∀ X0 X1 : G, (k X0 X0) = (k X1 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9381 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9381
    | (have j0 := eq9381 X0 X1
       grind)
    | exact resolve eq9381 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9381
  have eq9462 : ∀ X0 X1 : G, (k X0 X0) = (k X1 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9449 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9449
    | (have j0 := eq9449 X0 X1
       grind)
    | exact resolve eq9449 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9449
  have eq9573 : ∀ X0 X1 X2 : G, (M.op (σ (τ X1)) X2) = (M.op (σ (τ (k X0 X1))) X2) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq406 (τ X0) (τ X1) X2
       have i₂ := eq46 X1 X0
       grind)
    | exact superpose eq46 eq406
    | (have j0 := eq406 X0 (τ X1) X2
       grind)
    | exact resolve eq406 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq9813 : ∀ X0 X1 X2 : G, (M.op (σ (τ X1)) X2) = (M.op (k X0 X1) X2) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9573 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq9573
    | (have j0 := eq9573 X0 X1 X2
       grind)
    | exact resolve eq9573 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9573
  have eq9857 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (k X0 X1) X2) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9813 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq9813
    | (have j0 := eq9813 X0 X1 X2
       grind)
    | exact resolve eq9813 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9813
  have eq9878 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X2) = (M.op (k X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9857 X0 X0 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9857
    | (have j0 := eq9857 X0 X1 X2
       grind)
    | exact resolve eq9857 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9857
  have eq19684 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3597 (k X0 X0)
       have i₂ := eq9462 X0 (k X0 X0)
       grind)
    | exact superpose eq9462 eq3597
    | (have j0 := eq3597 (k X0 X0)
       have j1 := eq9462 (k X0 X0) x
       grind)
    | (have r₁ := eq3597 (k X0 X0)
       have r₂ := eq9462 X0 (k X0 X0)
       grind)
    | exact resolve eq3597 eq9462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3597 eq9462
  have eq19711 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq19684 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19684
  have eq81353 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq448 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq82715 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k X1 (τ (M.op X0 (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (M.op X0 (σ X1))
       have i₂ := eq81353 X0 (σ X1)
       grind)
    | exact superpose eq81353 eq28
    | exact resolve eq28 eq81353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109652 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9878 X0 X0 (k X0 X0)
       have i₂ := eq19711 X0
       grind)
    | exact superpose eq19711 eq9878
    | (have j0 := eq9878 X0 X0 x
       have j1 := eq19711 X0
       grind)
    | exact resolve eq9878 eq19711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9878 eq19711
  have eq109784 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq109652 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109652
  have eq111037 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X0) ∨ (M.op X0 X0) = (k X1 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq478 X0 (k X0 X0) x
       have i₂ := eq109784 X0
       grind)
    | exact superpose eq109784 eq478
    | (have j1 := eq109784 X0
       grind)
    | exact resolve eq478 eq109784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq111243 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq111037 X0 X1
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq111037 X0 X1
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq111037 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111037
  have eq114162 : ∀ X0 X1 X2 : G, (k X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq111243 X0 X1
       have i₂ := eq45 X0 X0 X2
       grind)
    | exact superpose eq45 eq111243
    | (have j0 := eq111243 X0 X1
       have j1 := eq45 X0 X1 X2
       grind)
    | exact resolve eq111243 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111243
  have eq114612 : ∀ X0 X1 X2 : G, (k X1 X0) = (M.op X0 X0) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq114162 X0 X1 X2
       have j1 := eq11 X1 X0
       grind)
    | (have r₁ := eq114162 X1 X1 X2
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq114162 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114162
  have eq117431 : ∀ X0 X1 X2 X3 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (k X2 X1) ∨ (M.op X1 X3) = (k X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq114612 X0 X1 X2
       grind)
    | exact superpose eq114612 eq11
    | (have j1 := eq114612 X1 X1 X3
       grind)
    | exact resolve eq11 eq114612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117938 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq114612 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114612
  have eq118107 : ∀ X0 X1 X2 X3 : G, (k X0 X1) = (k X2 X1) ∨ (M.op X1 X3) = (k X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq117431 X0 X1 X2 X3
       have j1 := eq45 X1 X1 X3
       grind)
    | (have r₁ := eq117431 X1 X0 X2 X3
       have r₂ := eq45 X0 X1 X2
       grind)
    | exact resolve eq117431 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq117431
  have eq119552 : ∀ X0 : G, (M.op X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq117938 (k X0 X0) X0
       have i₂ := eq109784 X0
       grind)
    | exact superpose eq109784 eq117938
    | (have j1 := eq109784 X0
       grind)
    | exact resolve eq117938 eq109784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109784
  have eq119722 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq117938 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117938
  have eq119834 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq119552 X0
       have j1 := eq118107 X0 X0 (k X0 X0) x
       grind)
    | (have r₁ := eq119552 x
       have r₂ := eq118107 X0 x x x
       grind)
    | exact resolve eq119552 eq118107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119552
  have eq119885 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq119834 X0
       have i₂ := eq119722 X0
       grind)
    | exact superpose eq119722 eq119834
    | (have j0 := eq119834 X0
       grind)
    | exact resolve eq119834 eq119722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119834
  have eq119931 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq119885 X0
       have j1 := eq11 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq119885 x
       have r₂ := eq11 X0 x
       grind)
    | exact resolve eq119885 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119885
  have eq121408 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq119722 (σ X0)
       grind)
    | exact superpose eq119722 eq13
    | exact resolve eq13 eq119722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121418 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46 X0 X0
       have i₂ := eq119722 (τ X0)
       grind)
    | exact superpose eq119722 eq46
    | exact resolve eq46 eq119722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq121474 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq121418 X0
       have i₂ := eq119722 X0
       grind)
    | exact superpose eq119722 eq121418
    | exact resolve eq121418 eq119722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121418
  have eq121480 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq121408 X0
       have i₂ := eq119722 X0
       grind)
    | exact superpose eq119722 eq121408
    | exact resolve eq121408 eq119722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119722 eq121408
  have eq122658 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k (M.op X0 (M.op X0 X1)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq119931 (M.op X0 x)
       have i₂ := eq306 X0 (M.op X0 x) x
       grind)
    | exact superpose eq306 eq119931
    | exact resolve eq119931 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119931
  have eq123095 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq122658 X1 x
       have i₂ := eq345 X1 X1 x
       grind)
    | exact superpose eq345 eq122658
    | exact resolve eq122658 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122658
  have eq124408 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq306 (τ X0) X1 (τ X0)
       have i₂ := eq121474 X0
       grind)
    | exact superpose eq121474 eq306
    | exact resolve eq306 eq121474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124418 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq345 X1 (τ X0) (τ X0)
       have i₂ := eq121474 X0
       grind)
    | exact superpose eq121474 eq345
    | exact resolve eq345 eq121474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121474
  have eq126139 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq306 (σ X0) X1 (σ X0)
       have i₂ := eq121480 X0
       grind)
    | exact superpose eq121480 eq306
    | exact resolve eq306 eq121480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121480
  have eq127721 : ∀ X0 : G, (σ x) = (k (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq123095 (σ x) x
       have i₂ := eq4396
       grind)
    | exact superpose eq4396 eq123095
    | exact resolve eq123095 eq4396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4396
  have eq127744 : ∀ X0 : G, x = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq123095 x x
       have i₂ := eq4557
       grind)
    | exact superpose eq4557 eq123095
    | exact resolve eq123095 eq4557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123095
  have eq130372 : ∀ X0 : G, (τ (σ x)) = (k x (τ (M.op (σ x) X0))) := by
    intro X0
    first
    | (have i₁ := eq28 x (M.op (σ x) X0)
       have i₂ := eq127721 X0
       grind)
    | exact superpose eq127721 eq28
    | exact resolve eq28 eq127721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq127721
  have eq130442 : ∀ X0 : G, x = (k x (τ (M.op (σ x) X0))) := by
    intro X0
    first
    | (have i₁ := eq130372 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq130372
    | exact resolve eq130372 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130372
  have eq135278 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 X1)) X2) = (M.op (τ (M.op X0 (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq124408 (M.op X0 X1) X2
       have i₂ := eq306 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq306 eq124408
    | exact resolve eq124408 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135879 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 X0)) X2) = (M.op (τ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq135278 X0 X1 X2
       have i₂ := eq345 X0 X0 X1
       grind)
    | exact superpose eq345 eq135278
    | exact resolve eq135278 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135278
  have eq136033 : ∀ X0 X1 X2 : G, (M.op (τ X0) X2) = (M.op (τ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq135879 X0 X1 X2
       have i₂ := eq124408 X0 X2
       grind)
    | exact superpose eq124408 eq135879
    | exact resolve eq135879 eq124408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124408 eq135879
  have eq137157 : ∀ X0 X1 X2 : G, (M.op X2 (τ (M.op X0 X1))) = (M.op X2 (τ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq124418 (M.op X0 X1) X2
       have i₂ := eq306 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq306 eq124418
    | exact resolve eq124418 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137740 : ∀ X0 X1 X2 : G, (M.op X2 (τ (M.op X0 X0))) = (M.op X2 (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq137157 X0 X1 X2
       have i₂ := eq345 X0 X0 X1
       grind)
    | exact superpose eq345 eq137157
    | exact resolve eq137157 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137157
  have eq137828 : ∀ X0 X1 X2 : G, (M.op X2 (τ X0)) = (M.op X2 (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq137740 X0 X1 X2
       have i₂ := eq124418 X0 X2
       grind)
    | exact superpose eq124418 eq137740
    | exact resolve eq137740 eq124418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124418 eq137740
  have eq138898 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X1)) X2) = (M.op (σ (M.op X0 (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq126139 (M.op X0 X1) X2
       have i₂ := eq306 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq306 eq126139
    | exact resolve eq126139 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139561 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X2) = (M.op (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq138898 X0 X1 X2
       have i₂ := eq345 X0 X0 X1
       grind)
    | exact superpose eq345 eq138898
    | exact resolve eq138898 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138898
  have eq139712 : ∀ X0 X1 X2 : G, (M.op (σ X0) X2) = (M.op (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq139561 X0 X1 X2
       have i₂ := eq126139 X0 X2
       grind)
    | exact superpose eq126139 eq139561
    | exact resolve eq139561 eq126139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126139 eq139561
  have eq144824 : ∀ X0 X1 X2 : G, (M.op X0 (τ X1)) = (k (τ (M.op X1 X2)) (M.op X0 (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81353 X2 (τ (M.op X0 X1))
       have i₂ := eq137828 X0 X1 X2
       grind)
    | exact superpose eq137828 eq81353
    | exact resolve eq81353 eq137828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81353 eq137828
  have eq168773 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ (k X2 X1) ∨ (k X0 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq118107 X0 X1 X2 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118107
  have eq170768 : ∀ X0 X1 : G, x ≠ (M.op (M.op x X0) X1) ∨ x = (k X1 (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq168773 X0 (M.op x X0) x
       have i₂ := eq127744 X0
       grind)
    | exact superpose eq127744 eq168773
    | exact resolve eq168773 eq127744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127744
  have eq170773 : ∀ X0 X1 : G, x ≠ (M.op (τ (M.op (σ x) X0)) X1) ∨ x = (k X1 (τ (M.op (σ x) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq168773 X0 (τ (M.op (σ x) X0)) x
       have i₂ := eq130442 X0
       grind)
    | exact superpose eq130442 eq168773
    | exact resolve eq168773 eq130442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130442 eq168773
  have eq170778 : ∀ X0 X1 : G, x ≠ (M.op (τ (σ x)) X1) ∨ x = (k X1 (τ (M.op (σ x) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq170773 X0 X1
       have i₂ := eq136033 (σ x) X0 X1
       grind)
    | exact superpose eq136033 eq170773
    | (have j0 := eq170773 X0 X1
       grind)
    | exact resolve eq170773 eq136033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136033 eq170773
  have eq170781 : ∀ X0 X1 : G, x ≠ (M.op x X1) ∨ x = (k X1 (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq170768 X0 X1
       have i₂ := eq306 x X1 X0
       grind)
    | exact superpose eq306 eq170768
    | (have j0 := eq170768 X0 X1
       grind)
    | exact resolve eq170768 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq170768
  have eq170840 : ∀ X0 X1 : G, x ≠ (M.op x X1) ∨ x = (k X1 (τ (M.op (σ x) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq170778 X0 X1
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq170778
    | (have j0 := eq170778 X0 X1
       grind)
    | exact resolve eq170778 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170778
  have eq171628 : ∀ X0 X1 X2 : G, x ≠ (M.op x X0) ∨ x = (k (M.op X0 X1) (M.op x X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq170781 X2 (M.op X0 X1)
       have i₂ := eq345 x X0 X1
       grind)
    | exact superpose eq345 eq170781
    | (have j0 := eq170781 X0 X0
       grind)
    | exact resolve eq170781 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170781
  have eq185234 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k (τ (M.op (σ X0) X2)) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq144824 X0 (σ X0) X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq144824
    | exact resolve eq144824 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144824
  have eq186138 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (k (M.op (σ X1) X2) (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (M.op (σ X1) X2) (M.op X0 X1)
       have i₂ := eq185234 X1 X0 X2
       grind)
    | exact superpose eq185234 eq15
    | exact resolve eq15 eq185234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq185234
  have eq190778 : ∀ X0 X1 : G, x ≠ x ∨ x = (k (M.op x X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq171628 x X0 X1
       have i₂ := eq4557
       grind)
    | exact superpose eq4557 eq171628
    | (have j0 := eq171628 x X0 X1
       grind)
    | (have r₁ := eq171628 x X1 x
       have r₂ := eq4557
       grind)
    | exact resolve eq171628 eq4557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4557 eq171628
  have eq190800 : ∀ X0 X1 : G, x = (k (M.op x X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have j0 := eq190778 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190778
  have eq191606 : ∀ X1 X2 : G, x = (M.op x X1) ∨ (k X2 (σ (M.op x X1))) = (M.op (σ (M.op x X1)) X2) := by
    intro X1 X2
    first
    | (have i₁ := eq1685 (M.op x X1) (M.op x x) X2
       have i₂ := eq190800 x X1
       grind)
    | exact superpose eq190800 eq1685
    | (have j0 := eq1685 (M.op x X1) X1 X2
       grind)
    | exact resolve eq1685 eq190800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1685 eq190800
  have eq191713 : ∀ X1 X2 : G, (M.op (σ x) X2) = (k X2 (σ (M.op x X1))) ∨ x = (M.op x X1) := by
    intro X1 X2
    first
    | (have i₁ := eq191606 X1 X2
       have i₂ := eq139712 x X1 X2
       grind)
    | exact superpose eq139712 eq191606
    | (have j0 := eq191606 X1 X2
       grind)
    | exact resolve eq191606 eq139712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139712 eq191606
  have eq750532 : ∀ X0 X1 : G, (σ (M.op x X0)) = (M.op (σ x) (M.op (σ X0) X1)) ∨ x = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq186138 x X0 X1
       have i₂ := eq191713 X0 (M.op (σ X0) X1)
       grind)
    | exact superpose eq191713 eq186138
    | (have j1 := eq191713 X0 x
       grind)
    | exact resolve eq186138 eq191713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186138 eq191713
  have eq750542 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) (σ X0)) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq750532 X0 x
       have i₂ := eq345 (σ x) (σ X0) x
       grind)
    | exact superpose eq345 eq750532
    | (have j0 := eq750532 X0 x
       grind)
    | exact resolve eq750532 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq750532
  have eq753588 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq750542 y
       grind)
    | exact superpose eq750542 eq14
    | (have j1 := eq750542 y
       grind)
    | (have r₁ := eq14
       have r₂ := eq750542 y
       grind)
    | exact resolve eq14 eq750542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750542
  have eq753643 : x = (M.op x y) := by grind
  clear eq753588
  have eq757253 : ∀ X0 : G, x ≠ x ∨ x = (k y (τ (M.op (σ x) X0))) := by
    intro X0
    first
    | (have i₁ := eq170840 X0 y
       have i₂ := eq753643
       grind)
    | exact superpose eq753643 eq170840
    | (have j0 := eq170840 X0 y
       grind)
    | (have r₁ := eq170840 X0 y
       have r₂ := eq753643
       grind)
    | exact resolve eq170840 eq753643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170840
  have eq757411 : ∀ X0 : G, x = (k y (τ (M.op (σ x) X0))) := by
    intro X0
    first
    | (have j0 := eq757253 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757253
  have eq777070 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq82715 (σ x) y
       have i₂ := eq757411 (σ y)
       grind)
    | exact superpose eq757411 eq82715
    | exact resolve eq82715 eq757411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82715 eq757411
  have eq779874 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ y))
       have i₂ := eq777070
       grind)
    | exact superpose eq777070 eq10
    | exact resolve eq10 eq777070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777070
  have eq782632 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq779874
       grind)
    | exact superpose eq779874 eq14
    | exact resolve eq14 eq779874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779874
  have eq782804 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq782632
       have i₂ := eq753643
       grind)
    | exact superpose eq753643 eq782632
    | exact resolve eq782632 eq753643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753643 eq782632
  have eq782805 : False := by grind
  exact eq782805

/-- `Equation3756`: `x ◇ y = (y ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pyx_Equation3756 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3756 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3756.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X2 X2) (M.op X1 X0) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X2) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 X1 X2 x
       have i₂ := eq8 X1 X0 x
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq34 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq37 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq42 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq51 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26
    | exact resolve eq26 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X0 (M.op X1 X2)) ∨ (M.op X0 X3) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X2 X1 X3
       have i₂ := eq12 X3 X0
       grind)
    | (have i₁ := eq21 X0 X1 X2
       have i₂ := eq12 X0 (M.op X2 X2)
       grind)
    | exact superpose eq12 eq21
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0 X1
       have i₂ := eq21 X1 X1 X0
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq96 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq160 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X1 (M.op X0 X0)
       have i₂ := eq96 X0 (σ X1)
       grind)
    | exact superpose eq96 eq42
    | exact resolve eq42 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq68 (σ X0) X1
       grind)
    | (have i₁ := eq34 X0 X0
       have i₂ := eq68 X0 (σ X0)
       grind)
    | exact superpose eq68 eq34
    | exact resolve eq34 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq34 X2 X0
       grind)
    | exact superpose eq34 eq13
    | (have j1 := eq34 X2 X0
       grind)
    | exact resolve eq13 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 X1) ∨ (M.op (σ X0) (σ X2)) = (σ (k X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X1 (σ X2)
       have i₂ := eq34 X0 X2
       grind)
    | exact superpose eq34 eq68
    | (have j1 := eq34 X0 X2
       grind)
    | exact resolve eq68 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq359 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X0)) = (σ (k X1 X2)) ∨ (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq332 X0 X1 X2
       have i₂ := eq96 (σ X0) (σ X1)
       grind)
    | exact superpose eq96 eq332
    | (have j0 := eq332 X0 X1 X2
       grind)
    | exact resolve eq332 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq467 : ∀ X0 X1 : G, (τ (τ (M.op X0 X0))) = (k X1 (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X1 (τ (M.op X0 X0))
       have i₂ := eq160 X0 (σ X1)
       grind)
    | exact superpose eq160 eq42
    | exact resolve eq42 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq160
  have eq991 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) ∨ (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq300 X1 (τ (τ (M.op X0 X0)))
       have i₂ := eq467 X0 (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq467 eq300
    | (have j0 := eq300 X1 (τ (τ (M.op X0 X0)))
       grind)
    | exact resolve eq300 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq992 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq300 X1 (M.op X0 X0)
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq300
    | (have j0 := eq300 X1 (M.op X0 X0)
       grind)
    | exact resolve eq300 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1029 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X1)) X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X1)
       have i₂ := eq300 X0 (τ X1)
       grind)
    | exact superpose eq300 eq17
    | (have j1 := eq300 X0 (τ X1)
       grind)
    | exact resolve eq17 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq1046 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq992 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq1047 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq991 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991
  have eq1061 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1029 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1029
    | (have j0 := eq1029 X0 X1
       grind)
    | exact resolve eq1029 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
  have eq1071 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1047 X0 X1
       have i₂ := eq10 (τ (M.op X0 X0))
       grind)
    | exact superpose eq10 eq1047
    | exact resolve eq1047 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047
  have eq1074 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1061 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1061
    | (have j0 := eq1061 X0 X1
       grind)
    | exact resolve eq1061 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061
  have eq1328 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1071 x X1
       have i₂ := eq1071 X0 x
       grind)
    | exact superpose eq1071 eq1071
    | exact resolve eq1071 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1403 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq37 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq37
    | exact resolve eq37 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq1509 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1403 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1403
    | (have j0 := eq1403 X0 X1
       grind)
    | exact resolve eq1403 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1403
  have eq9547 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X0)) = (k (σ X1) X2) ∨ (M.op (σ (τ X2)) (σ X0)) = (σ (k X0 (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X2 X1
       have i₂ := eq359 X0 X1 (τ X2)
       grind)
    | exact superpose eq359 eq17
    | (have j1 := eq359 X0 X1 (τ X2)
       grind)
    | exact resolve eq17 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq9711 : ∀ X0 X1 X2 : G, (k (σ X0) X2) = (M.op (σ (τ X2)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9547 X0 X1 X2
       have i₂ := eq17 X2 X0
       grind)
    | exact superpose eq17 eq9547
    | (have j0 := eq9547 X0 X1 X2
       grind)
    | exact resolve eq9547 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq9547
  have eq9774 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (k (σ X0) X2) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9711 X0 X1 X2
       have i₂ := eq10 X2
       grind)
    | exact superpose eq10 eq9711
    | (have j0 := eq9711 X0 X1 X2
       grind)
    | exact resolve eq9711 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9711
  have eq9870 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X1 X2
       have i₂ := eq1074 X2 X0
       grind)
    | exact superpose eq1074 eq68
    | (have j1 := eq1074 X1 X0
       grind)
    | exact resolve eq68 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1074
  have eq12152 : ∀ X0 X2 X3 : G, (k X2 X0) = X0 ∨ (M.op X3 X3) = (k X0 X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq96 X2 x
       have i₂ := eq9870 X0 x X2
       grind)
    | (have i₁ := eq96 X0 x
       have i₂ := eq9870 (M.op X0 X0) x X2
       grind)
    | exact superpose eq9870 eq96
    | (have j1 := eq9870 X0 X3 X2
       grind)
    | exact resolve eq96 eq9870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq13496 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12152 X0 x X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12152
  have eq13506 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq13496 X0 X1
       have j1 := eq9870 X0 X1 x
       grind)
    | (have r₁ := eq13496 (k X0 X0) X1
       have r₂ := eq9870 X0 X1 x
       grind)
    | (have r₁ := eq13496 X0 x
       have r₂ := eq9870 X0 X1 x
       grind)
    | (have r₁ := eq13496 (M.op x x) X1
       have r₂ := eq9870 (M.op X1 X1) X1 x
       grind)
    | exact resolve eq13496 eq9870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9870 eq13496
  have eq14216 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1328 x X1
       have i₂ := eq13506 X0 x
       grind)
    | exact superpose eq13506 eq1328
    | exact resolve eq1328 eq13506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328
  have eq14360 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 X1
       have i₂ := eq13506 (τ X1) X0
       grind)
    | exact superpose eq13506 eq51
    | exact resolve eq51 eq13506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq13506
  have eq37974 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 X1) ∨ (σ (k X2 X0)) = (σ (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1046 X2 X1
       have i₂ := eq1509 X0 X2
       grind)
    | (have i₁ := eq1046 X0 X1
       have i₂ := eq1509 (M.op X0 X0) X1
       grind)
    | exact superpose eq1509 eq1046
    | (have j1 := eq1509 X0 X2
       grind)
    | exact resolve eq1046 eq1509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046 eq1509
  have eq55782 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq346 x X0 y
       grind)
    | exact superpose eq346 eq14
    | (have j1 := eq346 x X0 x
       grind)
    | exact resolve eq14 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq55990 : ∀ X0 : G, (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq55782 X0
       have j1 := eq37974 x X0 x
       grind)
    | (have r₁ := eq55782 X0
       have r₂ := eq37974 x x y
       grind)
    | exact resolve eq55782 eq37974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37974 eq55782
  have eq56252 : ∀ X0 : G, (M.op X0 X0) = (τ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1071 x X0
       have i₂ := eq55990 x
       grind)
    | exact superpose eq55990 eq1071
    | exact resolve eq1071 eq55990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071
  have eq56314 : ∀ X1 : G, (σ x) = (τ (τ (k X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq14216 X1 x
       have i₂ := eq55990 x
       grind)
    | exact superpose eq55990 eq14216
    | exact resolve eq14216 eq55990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14216
  have eq56330 : ∀ X1 : G, (σ x) = (τ (k X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq14360 x X1
       have i₂ := eq55990 x
       grind)
    | exact superpose eq55990 eq14360
    | exact resolve eq14360 eq55990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14360
  have eq56478 : (σ x) = (τ (σ x)) := by
    first
    | (have i₁ := eq56314 x
       have i₂ := eq56330 x
       grind)
    | exact superpose eq56330 eq56314
    | exact resolve eq56314 eq56330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56314 eq56330
  have eq56521 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq56252 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq56252
    | exact resolve eq56252 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56252
  have eq56566 : x = (σ x) := by
    first
    | (have i₁ := eq56478
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq56478
    | exact resolve eq56478 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56478
  have eq57545 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq56566
       grind)
    | exact superpose eq56566 eq14
    | exact resolve eq14 eq56566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57547 : ∀ X0 : G, (σ (k x X0)) = (k x (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq56566
       grind)
    | exact superpose eq56566 eq13
    | exact resolve eq13 eq56566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59980 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq56521 x
       grind)
    | exact superpose eq56521 eq8
    | exact resolve eq8 eq56521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60102 : ∀ X1 X2 : G, (M.op X1 X2) = (k X2 X1) ∨ x = (M.op X1 x) := by
    intro X1 X2
    first
    | (have i₁ := eq62 x x x x
       have i₂ := eq56521 x
       grind)
    | exact superpose eq56521 eq62
    | (have j0 := eq62 X1 X1 X2 X2
       grind)
    | exact resolve eq62 eq56521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq56521
  have eq99184 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq9774 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9774
  have eq99185 : ∀ X0 X1 : G, (σ x) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq99184 X0 X1
       have i₂ := eq55990 (σ X0)
       grind)
    | exact superpose eq55990 eq99184
    | (have j0 := eq99184 X0 X1
       grind)
    | exact resolve eq99184 eq55990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55990 eq99184
  have eq99279 : ∀ X0 X1 : G, x ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq99185 X0 X1
       have i₂ := eq56566
       grind)
    | exact superpose eq56566 eq99185
    | (have j0 := eq99185 X0 X1
       grind)
    | exact resolve eq99185 eq56566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99185
  have eq530757 : ∀ X0 : G, x ≠ (M.op X0 x) ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq99279 x x
       have i₂ := eq56566
       grind)
    | exact superpose eq56566 eq99279
    | exact resolve eq99279 eq56566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56566 eq99279
  have eq530788 : ∀ X0 : G, (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq530757 X0
       have j1 := eq60102 X0 x
       grind)
    | (have r₁ := eq530757 x
       have r₂ := eq60102 x x
       grind)
    | exact resolve eq530757 eq60102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60102 eq530757
  have eq530918 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) x) := by
    intro X0
    first
    | (have i₁ := eq57547 X0
       have i₂ := eq530788 (σ X0)
       grind)
    | exact superpose eq530788 eq57547
    | exact resolve eq57547 eq530788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq531338 : ∀ X0 : G, (M.op (σ X0) x) = (σ (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq530918 X0
       have i₂ := eq530788 X0
       grind)
    | exact superpose eq530788 eq530918
    | exact resolve eq530918 eq530788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530918
  have eq531457 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X1 X0)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq531338 (M.op X1 X0)
       have i₂ := eq59980 X0 X1
       grind)
    | exact superpose eq59980 eq531338
    | exact resolve eq531338 eq59980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq531668 : ∀ X0 : G, (k x (M.op (σ X0) x)) = (σ (k x (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq57547 (M.op X0 x)
       have i₂ := eq531338 X0
       grind)
    | exact superpose eq531338 eq57547
    | exact resolve eq57547 eq531338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57547
  have eq531686 : ∀ X0 : G, (k x (M.op (σ X0) x)) = (σ (M.op (M.op X0 x) x)) := by
    intro X0
    first
    | (have i₁ := eq531668 X0
       have i₂ := eq530788 (M.op X0 x)
       grind)
    | exact superpose eq530788 eq531668
    | exact resolve eq531668 eq530788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531668
  have eq531868 : ∀ X0 : G, (k x (M.op (σ X0) x)) = (M.op (σ (M.op X0 x)) x) := by
    intro X0
    first
    | (have i₁ := eq531686 X0
       have i₂ := eq531338 (M.op X0 x)
       grind)
    | exact superpose eq531338 eq531686
    | exact resolve eq531686 eq531338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531338 eq531686
  have eq531989 : ∀ X0 : G, (σ (M.op x X0)) = (k x (M.op (σ X0) x)) := by
    intro X0
    first
    | (have i₁ := eq531868 X0
       have i₂ := eq531457 x X0
       grind)
    | exact superpose eq531457 eq531868
    | exact resolve eq531868 eq531457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531457 eq531868
  have eq532078 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (M.op (σ X0) x) x) := by
    intro X0
    first
    | (have i₁ := eq531989 X0
       have i₂ := eq530788 (M.op (σ X0) x)
       grind)
    | exact superpose eq530788 eq531989
    | exact resolve eq531989 eq530788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530788 eq531989
  have eq532145 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq532078 X0
       have i₂ := eq59980 x (σ X0)
       grind)
    | exact superpose eq59980 eq532078
    | exact resolve eq532078 eq59980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59980 eq532078
  have eq533480 : (M.op x (σ y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq57545
       have i₂ := eq532145 y
       grind)
    | exact superpose eq532145 eq57545
    | (have r₁ := eq57545
       have r₂ := eq532145 y
       grind)
    | exact resolve eq57545 eq532145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57545 eq532145
  have eq533649 : False := by grind
  exact eq533649

/-- `Equation4388`: `x ◇ (x ◇ x) = (y ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4388 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4388 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4388.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) X0) := by
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
  have eq18 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq8 X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq24 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq20 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20
    | exact resolve eq20 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq29 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq31 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq34 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq68 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) (M.op (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1
    grind
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq29
    | exact resolve eq29 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq90 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq24 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq24
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq133 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq39
  have eq148 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq133 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq133
    | exact resolve eq133 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq281 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq148 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq148 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq148
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq148 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq31 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq31
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq31 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq333 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq31 x y
       grind)
    | exact superpose eq31 eq14
    | (have j1 := eq31 x y
       grind)
    | exact resolve eq14 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq347 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq9
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq338 X0
       have i₂ := eq13 X0 (k X0 X0)
       grind)
    | exact superpose eq13 eq338
    | (have j0 := eq338 X0
       grind)
    | exact resolve eq338 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq953 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq1042 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq953 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq953
    | (have j0 := eq953 X0 X1
       grind)
    | exact resolve eq953 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953
  have eq1107 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq2014 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq14
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq14 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2015 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq79 X0 X0
       grind)
    | exact superpose eq79 eq31
    | (have j0 := eq31 X0 X1
       have j1 := eq79 X0 X1
       grind)
    | exact resolve eq31 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq2018 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) X1
       have i₂ := eq79 X0 X0
       grind)
    | exact superpose eq79 eq8
    | (have j1 := eq79 X0 X0
       grind)
    | exact resolve eq8 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2020 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq79 X0 X0
       grind)
    | exact superpose eq79 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq79 X0 X0
       grind)
    | exact resolve eq12 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq2282 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq333
       have i₂ := eq1107 y x
       grind)
    | exact superpose eq1107 eq333
    | (have j1 := eq1107 y x
       grind)
    | (have r₁ := eq333
       have r₂ := eq1107 y x
       grind)
    | exact resolve eq333 eq1107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq2283 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq333
       have i₂ := eq1042 y x
       grind)
    | exact superpose eq1042 eq333
    | (have j1 := eq1042 (σ y) (σ x)
       grind)
    | (have r₁ := eq333
       have r₂ := eq1042 y x
       grind)
    | exact resolve eq333 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq2284 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2283
  have eq2285 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq2282
  have eq2295 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq148 x
       have i₂ := eq2284
       grind)
    | exact superpose eq2284 eq148
    | exact resolve eq148 eq2284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2317 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq85 (σ x) (σ x)
       have i₂ := eq2284
       grind)
    | exact superpose eq2284 eq85
    | (have j0 := eq85 (σ x) (σ x)
       grind)
    | exact resolve eq85 eq2284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq2319 : (σ x) = (σ (k x x)) ∨ (σ x) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2317
       have i₂ := eq13 x x
       grind)
    | exact superpose eq13 eq2317
    | exact resolve eq2317 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2317
  have eq2322 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2295
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2295
    | exact resolve eq2295 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2295
  have eq2407 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1042 y x
       have i₂ := eq2322
       grind)
    | exact superpose eq2322 eq1042
    | (have j0 := eq1042 y x
       grind)
    | exact resolve eq1042 eq2322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042 eq2322
  have eq2408 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq2407
  have eq3261 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq148 x
       have i₂ := eq2285
       grind)
    | exact superpose eq2285 eq148
    | exact resolve eq148 eq2285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq2285
  have eq3296 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq3261
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3261
    | exact resolve eq3261 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3261
  have eq3297 : x = (k x y) := by grind
  clear eq3296
  have eq4199 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq90
    | (have j0 := eq90 X1 (σ X0)
       grind)
    | exact resolve eq90 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq4274 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4199 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq4199
    | (have j0 := eq4199 X0 X1
       grind)
    | exact resolve eq4199 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4199
  have eq12744 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 (τ (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) X1
       have i₂ := eq281 (σ X1) X0
       grind)
    | exact superpose eq281 eq23
    | (have j1 := eq281 (σ X1) X0
       grind)
    | exact resolve eq23 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq12774 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 (τ (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12744 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq12744
    | (have j0 := eq12744 X0 X1
       grind)
    | exact resolve eq12744 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12744
  have eq12813 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12774 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq12774
    | (have j0 := eq12774 X0 X1
       grind)
    | exact resolve eq12774 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12774
  have eq33983 : (k x x) = (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12813 x x
       have i₂ := eq2284
       grind)
    | exact superpose eq2284 eq12813
    | (have j0 := eq12813 x x
       grind)
    | exact resolve eq12813 eq2284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12813
  have eq34072 : y = (k x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq33983
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq33983
    | exact resolve eq33983 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33983
  have eq42409 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4274 x x
       have i₂ := eq34072
       grind)
    | exact superpose eq34072 eq4274
    | exact resolve eq4274 eq34072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4274 eq34072
  have eq42413 : x = (k x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq42409
  have eq53884 : (σ x) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq379 x
       have i₂ := eq42413
       grind)
    | exact superpose eq42413 eq379
    | (have j0 := eq379 x
       grind)
    | exact resolve eq379 eq42413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379 eq42413
  have eq53921 : (σ x) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq53884
       have r₂ := eq2319
       grind)
    | exact resolve eq53884 eq2319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2319 eq53884
  have eq53925 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq370 x
       grind)
    | (have r₁ := eq53921
       have r₂ := eq370 x
       grind)
    | exact resolve eq53921 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53921
  have eq55078 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2284
       have i₂ := eq53925
       grind)
    | exact superpose eq53925 eq2284
    | exact resolve eq2284 eq53925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55098 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 (σ x)
       have i₂ := eq53925
       grind)
    | exact superpose eq53925 eq8
    | exact resolve eq8 eq53925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53925
  have eq55174 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq55078
  have eq56135 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y X0) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq8 X0 x
       have i₂ := eq55174
       grind)
    | exact superpose eq55174 eq8
    | exact resolve eq8 eq55174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59605 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq56135 x
       have i₂ := eq55174
       grind)
    | exact superpose eq55174 eq56135
    | exact resolve eq56135 eq55174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56135
  have eq59670 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq59605
  have eq65106 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq55098 (σ x)
       have i₂ := eq2284
       grind)
    | exact superpose eq2284 eq55098
    | exact resolve eq55098 eq2284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2284 eq55098
  have eq65218 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq65106
  have eq65255 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq65218
       grind)
    | exact superpose eq65218 eq14
    | exact resolve eq14 eq65218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65218
  have eq65315 : (σ x) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq65255
       have i₂ := eq2408
       grind)
    | exact superpose eq2408 eq65255
    | exact resolve eq65255 eq2408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2408 eq65255
  have eq65317 : (σ x) ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq65315
  have eq65319 : y = (M.op x x) := by
    first
    | (have r₁ := eq65317
       have r₂ := eq55174
       grind)
    | exact resolve eq65317 eq55174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55174 eq65317
  have eq65358 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq8 X0 x
       have i₂ := eq65319
       grind)
    | exact superpose eq65319 eq8
    | exact resolve eq8 eq65319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65361 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 x
       have i₂ := eq65319
       grind)
    | exact superpose eq65319 eq18
    | exact resolve eq18 eq65319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq65375 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op y (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq68 x X0
       have i₂ := eq65319
       grind)
    | exact superpose eq65319 eq68
    | exact resolve eq68 eq65319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq71262 : (M.op y y) = (k (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq65375 y
       have i₂ := eq65358 y
       grind)
    | exact superpose eq65358 eq65375
    | exact resolve eq65375 eq65358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65358 eq65375
  have eq71319 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
    first
    | (have i₁ := eq370 (M.op y y)
       have i₂ := eq71262
       grind)
    | exact superpose eq71262 eq370
    | (have j0 := eq370 (M.op y y)
       grind)
    | exact resolve eq370 eq71262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71349 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by grind
  clear eq71319
  have eq75336 : ∀ X0 : G, (τ (σ (M.op y y))) = X0 ∨ (σ (k (M.op y y) X0)) = (M.op (σ (M.op y y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq347 (M.op y y) X0
       have i₂ := eq71349
       grind)
    | exact superpose eq71349 eq347
    | (have j0 := eq347 (M.op y y) X0
       grind)
    | exact resolve eq347 eq71349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq75474 : ∀ X0 : G, (M.op y X0) = (M.op (σ (M.op y y)) X0) := by
    intro X0
    first
    | (have i₁ := eq65361 (σ (M.op y y)) X0
       have i₂ := eq71349
       grind)
    | exact superpose eq71349 eq65361
    | exact resolve eq65361 eq71349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75611 : ∀ X0 : G, (M.op y y) = X0 ∨ (σ (k (M.op y y) X0)) = (M.op (σ (M.op y y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq75336 X0
       have i₂ := eq9 (M.op y y)
       grind)
    | exact superpose eq9 eq75336
    | (have j0 := eq75336 X0
       grind)
    | exact resolve eq75336 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75336
  have eq75673 : ∀ X0 : G, (M.op y (σ X0)) = (σ (k (M.op y y) X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq75611 X0
       have i₂ := eq75474 (σ X0)
       grind)
    | exact superpose eq75474 eq75611
    | (have j0 := eq75611 X0
       grind)
    | exact resolve eq75611 eq75474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75474 eq75611
  have eq78200 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq2020 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2020
  have eq78201 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq78200 X0 X1
       have j1 := eq318 X1 X0
       grind)
    | (have r₁ := eq78200 (k X1 X1) X0
       have r₂ := eq318 X0 X1
       grind)
    | (have r₁ := eq78200 X0 (σ (k X1 X1))
       have r₂ := eq318 (σ X0) X1
       grind)
    | (have r₁ := eq78200 X1 X0
       have r₂ := eq318 X0 X1
       grind)
    | exact resolve eq78200 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318 eq78200
  have eq78248 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq78201 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq78201 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq78201 eq16
    | (have j1 := eq78201 (τ X1) X0
       grind)
    | exact resolve eq16 eq78201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq78249 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq78201 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq78201 X0 (σ X0)
       grind)
    | exact superpose eq78201 eq9
    | (have j1 := eq78201 X1 X0
       grind)
    | exact resolve eq9 eq78201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78201
  have eq78268 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq78248 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq78248
    | (have j0 := eq78248 X0 X1
       grind)
    | exact resolve eq78248 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78248
  have eq78277 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq78268 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq78268
    | (have j0 := eq78268 X0 X1
       grind)
    | exact resolve eq78268 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78268
  have eq78432 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq78277 (τ X1) X0
       grind)
    | exact superpose eq78277 eq17
    | (have j1 := eq78277 (τ X1) X0
       grind)
    | exact resolve eq17 eq78277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq78472 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq2014
       have i₂ := eq78277 y x
       grind)
    | exact superpose eq78277 eq2014
    | (have j1 := eq78277 y x
       grind)
    | exact resolve eq2014 eq78277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2014 eq78277
  have eq78599 : (σ (M.op x y)) = (σ x) ∨ y = (k x x) := by grind
  clear eq78472
  have eq80736 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq78249 (σ X1) X0
       grind)
    | exact superpose eq78249 eq13
    | (have j1 := eq78249 (σ X1) X0
       grind)
    | exact resolve eq13 eq78249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80740 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) X1
       have i₂ := eq78249 (σ X1) X0
       grind)
    | exact superpose eq78249 eq23
    | (have j1 := eq78249 (σ X1) X0
       grind)
    | exact resolve eq23 eq78249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq78249
  have eq80742 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq80740 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq80740
    | (have j0 := eq80740 X0 X1
       grind)
    | exact resolve eq80740 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80740
  have eq80744 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq80736 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq80736
    | (have j0 := eq80736 X0 X1
       grind)
    | exact resolve eq80736 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80736
  have eq80773 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq80742 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq80742
    | (have j0 := eq80742 X0 X1
       grind)
    | exact resolve eq80742 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80742
  have eq81732 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq80744 x y
       grind)
    | exact superpose eq80744 eq14
    | (have j1 := eq80744 x y
       grind)
    | exact resolve eq14 eq80744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80744
  have eq81816 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq81732
       have i₂ := eq3297
       grind)
    | exact superpose eq3297 eq81732
    | exact resolve eq81732 eq3297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3297 eq81732
  have eq81838 : y = (k x x) := by
    first
    | (have r₁ := eq81816
       have r₂ := eq78599
       grind)
    | exact resolve eq81816 eq78599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78599 eq81816
  have eq81911 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq370 x
       have i₂ := eq81838
       grind)
    | exact superpose eq81838 eq370
    | (have j0 := eq370 x
       grind)
    | exact resolve eq370 eq81838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq81925 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X0) (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq2018 x x
       have i₂ := eq81838
       grind)
    | exact superpose eq81838 eq2018
    | exact resolve eq2018 eq81838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2018
  have eq82005 : (M.op (σ x) (σ y)) = (M.op y (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq81925 x
       have i₂ := eq65361 x (σ x)
       grind)
    | exact superpose eq65361 eq81925
    | exact resolve eq81925 eq65361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81925
  have eq88307 : (σ (M.op x y)) ≠ (M.op y (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq82005
       grind)
    | exact superpose eq82005 eq14
    | exact resolve eq14 eq82005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82005
  have eq108866 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq78432 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq78432
    | exact resolve eq78432 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78432
  have eq108935 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq108866 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq108866
    | (have j0 := eq108866 X0 X1
       grind)
    | exact resolve eq108866 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108866
  have eq109103 : ∀ X0 : G, (M.op y y) = X0 ∨ (σ (k (M.op y y) X0)) = (σ (M.op (M.op y y) X0)) := by
    intro X0
    first
    | (have i₁ := eq71262
       have i₂ := eq108935 X0 (M.op y y)
       grind)
    | (have i₁ := eq71262
       have i₂ := eq108935 (k (M.op y y) (M.op y y)) x
       grind)
    | exact superpose eq108935 eq71262
    | (have j1 := eq108935 X0 (M.op y y)
       grind)
    | exact resolve eq71262 eq108935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71262 eq108935
  have eq109117 : ∀ X0 : G, (σ (M.op y X0)) = (σ (k (M.op y y) X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq109103 X0
       have i₂ := eq65361 y X0
       grind)
    | exact superpose eq65361 eq109103
    | (have j0 := eq109103 X0
       grind)
    | exact resolve eq109103 eq65361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65361 eq109103
  have eq118141 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ (M.op y y) = X0 ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq109117 X0
       have i₂ := eq75673 X0
       grind)
    | exact superpose eq75673 eq109117
    | (have j0 := eq109117 X0
       have j1 := eq75673 X0
       grind)
    | exact resolve eq109117 eq75673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75673 eq109117
  have eq118152 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have j0 := eq118141 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118141
  have eq118182 : (σ (M.op x y)) = (M.op y (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq118152 x
       have i₂ := eq59670
       grind)
    | exact superpose eq59670 eq118152
    | (have j0 := eq118152 x
       grind)
    | exact resolve eq118152 eq59670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59670 eq118152
  have eq118256 : x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq118182
       have r₂ := eq88307
       grind)
    | exact resolve eq118182 eq88307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88307 eq118182
  have eq118283 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq71349
       have i₂ := eq118256
       grind)
    | exact superpose eq118256 eq71349
    | exact resolve eq71349 eq118256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71349 eq118256
  have eq118554 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq118283
       have r₂ := eq81911
       grind)
    | exact resolve eq118283 eq81911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81911 eq118283
  have eq118709 : (σ x) = (σ (k x x)) ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq2015 x x
       have i₂ := eq118554
       grind)
    | exact superpose eq118554 eq2015
    | (have j0 := eq2015 x x
       grind)
    | exact resolve eq2015 eq118554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2015
  have eq118716 : (k x x) = (τ (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq80773 x x
       have i₂ := eq118554
       grind)
    | exact superpose eq118554 eq80773
    | (have j0 := eq80773 x (τ (σ x))
       grind)
    | exact resolve eq80773 eq118554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80773
  have eq119003 : (σ x) = (σ (k x x)) := by grind
  clear eq118709
  have eq119219 : x = (k x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq118716
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq118716
    | exact resolve eq118716 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118716
  have eq119220 : x = (k x x) := by grind
  clear eq119219
  have eq119228 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq119003
       have i₂ := eq81838
       grind)
    | exact superpose eq81838 eq119003
    | exact resolve eq119003 eq81838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119003
  have eq119533 : x = y := by
    first
    | (have i₁ := eq81838
       have i₂ := eq119220
       grind)
    | exact superpose eq119220 eq81838
    | exact resolve eq81838 eq119220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81838 eq119220
  have eq119796 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq119533
       grind)
    | exact superpose eq119533 eq14
    | exact resolve eq14 eq119533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119533
  have eq120107 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq119796
       have i₂ := eq65319
       grind)
    | exact superpose eq65319 eq119796
    | exact resolve eq119796 eq65319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65319 eq119796
  have eq120166 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq120107
       have i₂ := eq118554
       grind)
    | exact superpose eq118554 eq120107
    | exact resolve eq120107 eq118554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118554 eq120107
  have eq120190 : False := by grind
  exact eq120190

/-- `Equation4407`: `x ◇ (x ◇ y) = (y ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation4407 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4407 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4407.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq72 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq442 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq446 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq442 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq442 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq442 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq442 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq483 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq446 (σ X0) (σ X1)
       grind)
    | exact superpose eq446 eq13
    | exact resolve eq13 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq490 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq483 X0 X1
       have i₂ := eq446 X0 X1
       grind)
    | exact superpose eq446 eq483
    | exact resolve eq483 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq483
  have eq1187 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq490 x y
       grind)
    | exact superpose eq490 eq14
    | (have r₁ := eq14
       have r₂ := eq490 x y
       grind)
    | exact resolve eq14 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq1210 : False := by grind
  exact eq1210

/-- `Equation4444`: `x ◇ (y ◇ x) = (y ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_y_x_pxy_Equation4444 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4444 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4444.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X0) X2) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq17 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X0 X3
       have i₂ := eq8 X1 X0 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X1 X0) X0 X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X1 X0))) = (M.op (M.op X0 (M.op X1 X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X1 X0) X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X2 (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X1 (M.op X0 (M.op X1 X2))
       have i₂ := eq8 (M.op X1 X2) X0 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X0 X1 X2 x
       have i₂ := eq21 X0 X1 X0 x
       grind)
    | exact superpose eq21 eq20
    | exact resolve eq20 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X0 X1 X2 X3
       have i₂ := eq8 X1 X0 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq31 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq32 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq62 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq72 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X0 X1 X0 X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq21
    | exact resolve eq21 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 X3 X4 X5 : G, (M.op X4 (M.op X3 X4)) = (M.op (M.op X0 (M.op X1 X0)) X5) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq21 (M.op x (M.op X1 X0)) X3 X4 X5
       have i₂ := eq21 x X1 X0 (M.op X3 X4)
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op X4 (M.op X3 X4)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq76 X4 X3 X1 X0 x
       have i₂ := eq21 X4 X3 X4 x
       grind)
    | exact superpose eq21 eq76
    | exact resolve eq76 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq76
  have eq154 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq17 X2 X3 (M.op X0 (M.op X1 X0)) X4
       have i₂ := eq24 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq24 eq17
    | exact resolve eq17 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op X0 X1) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X1 X0 X4
       have i₂ := eq25 X0 X1 X2 X3
       grind)
    | exact superpose eq25 eq8
    | exact resolve eq8 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op (M.op X1 X0) X2) ∨ (k X3 (M.op (M.op X1 X0) X2)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 X3 (M.op (M.op X1 X0) X2)
       have i₂ := eq25 X1 X0 X2 X3
       grind)
    | exact superpose eq25 eq11
    | (have j0 := eq11 X3 (M.op (M.op X1 X0) X2)
       grind)
    | exact resolve eq11 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq236 : ∀ X0 X1 X2 X3 : G, (k X3 (M.op (M.op X1 X0) X2)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq230 X0 X1 X2 X3
       grind)
    | (have r₁ := eq230 X0 X1 X2 X3
       have r₂ := eq8 X0 X1 X2
       grind)
    | exact resolve eq230 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq273 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X1 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq236 x x (M.op X0 (M.op X1 X0)) X2
       have i₂ := eq24 X0 X1 (M.op x x)
       grind)
    | exact superpose eq24 eq236
    | exact resolve eq236 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq327 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (M.op X2 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 (M.op X1 (M.op X2 X1))
       have i₂ := eq273 X1 X2 (τ X0)
       grind)
    | exact superpose eq273 eq15
    | exact resolve eq15 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq329 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (M.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq327 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq327
    | exact resolve eq327 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq400 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X0
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq31
    | (have j0 := eq31 X1 X0
       have j1 := eq31 X1 X0
       grind)
    | exact resolve eq31 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq31 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq31 X0 X1
       grind)
    | exact resolve eq11 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412 : ∀ X0 X1 X2 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) X2) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (σ X0) (σ X1) X2
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq8
    | (have j1 := eq31 X1 X0
       grind)
    | exact resolve eq8 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq413 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq31 X1 X0
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq31 X0 X1
       grind)
    | exact resolve eq11 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq414 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) X2) = (M.op (σ X0) X3) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17 (σ X1) (σ X0) X2 X3
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq17
    | (have j1 := eq31 X1 X0
       grind)
    | exact resolve eq17 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq424 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq413 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq426 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq424 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq424
    | (have j0 := eq424 X0 X1
       grind)
    | exact resolve eq424 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq428 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq402 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq402
    | (have j0 := eq402 X0 X1
       grind)
    | exact resolve eq402 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq661 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 X1)) = (M.op (σ X0) X4) ∨ (M.op (σ X3) (σ X0)) = (σ (k X3 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq154 X1 X2 (σ X0) (σ X3) X4
       have i₂ := eq31 X3 X0
       grind)
    | exact superpose eq31 eq154
    | (have j1 := eq31 X3 X0
       grind)
    | exact resolve eq154 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq154
  have eq6896 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) X2)) ≠ (σ (M.op (M.op X0 X1) X2)) ∨ (σ (M.op (M.op X0 X1) X2)) = (M.op (σ (M.op (M.op X0 X1) X2)) (σ (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq423 (M.op (M.op X0 X1) X2)
       have i₂ := eq236 X1 X0 X2 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq236 eq423
    | (have j0 := eq423 (M.op (M.op X0 X1) X2)
       grind)
    | exact resolve eq423 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq423
  have eq6931 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) X2)) = (M.op (σ (M.op (M.op X0 X1) X2)) (σ (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq6896 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6896
  have eq6982 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq32
    | exact resolve eq32 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq7042 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6982 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq6982
    | (have j0 := eq6982 X0 X1
       grind)
    | exact resolve eq6982 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6982
  have eq9318 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq426 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq426
    | exact resolve eq426 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq9400 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9318 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9318
    | (have j0 := eq9318 X0 X1
       grind)
    | exact resolve eq9318 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9318
  have eq9402 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9400 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9400
    | (have j0 := eq9400 X0 X1
       grind)
    | exact resolve eq9400 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9400
  have eq10348 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 (M.op X3 X2)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (M.op (σ X1) X4) = (M.op (σ X1) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq111 X2 X3 (σ X0) (σ X1)
       have i₂ := eq414 X1 X0 X4 X5
       grind)
    | exact superpose eq414 eq111
    | (have j1 := eq414 X1 X1 X4 X5
       grind)
    | exact resolve eq111 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq11111 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9402 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9402
    | exact resolve eq9402 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9402
  have eq11455 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11111 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11638 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op (M.op X0 X1) X2) ∨ (M.op (M.op X0 X1) X2) = (k (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11455 (M.op (M.op X0 X1) X2) X3
       have i₂ := eq72 X0 X1 X2 X3
       grind)
    | exact superpose eq72 eq11455
    | (have j0 := eq11455 (M.op (M.op X0 X1) X2) X3
       grind)
    | (have r₁ := eq11455 (M.op (M.op X0 X1) X2) X3
       have r₂ := eq72 X0 X1 X2 X3
       grind)
    | exact resolve eq11455 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq11651 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (k (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq11638 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11638
  have eq12223 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) X2) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq412 X1 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq15592 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq428 (τ X0) (τ X1)
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq428
    | (have j0 := eq428 (τ X0) (τ X1)
       grind)
    | exact resolve eq428 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq15626 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15592 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq15592
    | (have j0 := eq15592 X0 X1
       grind)
    | exact resolve eq15592 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15592
  have eq15642 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15626 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15626
    | (have j0 := eq15626 X0 X1
       grind)
    | exact resolve eq15626 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15626
  have eq15655 : ∀ X0 X1 : G, (σ (τ X1)) = (k (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15642 X0 X1
       have i₂ := eq16 X0 (τ X1)
       grind)
    | exact superpose eq16 eq15642
    | (have j0 := eq15642 X0 X1
       grind)
    | exact resolve eq15642 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15642
  have eq15664 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15655 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15655
    | (have j0 := eq15655 X0 X1
       grind)
    | exact resolve eq15655 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15655
  have eq15671 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15664 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15664
    | (have j0 := eq15664 X0 X1
       grind)
    | exact resolve eq15664 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15664
  have eq15672 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15671 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15671
    | (have j0 := eq15671 X0 X1
       grind)
    | exact resolve eq15671 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15671
  have eq15673 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq15672 X0 X1
       have j1 := eq11455 X1 X0
       grind)
    | (have r₁ := eq15672 X1 X0
       have r₂ := eq11455 X0 X1
       grind)
    | (have r₁ := eq15672 X0 X1
       have r₂ := eq11455 X0 X1
       grind)
    | exact resolve eq15672 eq11455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15672
  have eq20759 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq400 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq400
    | exact resolve eq400 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq20897 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20759 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq20759
    | (have j0 := eq20759 X0 X1
       grind)
    | exact resolve eq20759 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq20759
  have eq20899 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20897 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq20897
    | (have j0 := eq20897 X0 X1
       grind)
    | exact resolve eq20897 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq20897
  have eq20901 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq20899 X0 X1
       have j1 := eq11 X0 (σ X1)
       grind)
    | (have r₁ := eq20899 X0 X1
       have r₂ := eq11 X0 (σ X1)
       grind)
    | exact resolve eq20899 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20899
  have eq20971 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 (σ X1)
       have i₂ := eq20901 (σ X0) X1
       grind)
    | exact superpose eq20901 eq39
    | (have j1 := eq20901 (σ X0) X1
       grind)
    | exact resolve eq39 eq20901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq20901
  have eq21066 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20971 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq20971
    | (have j0 := eq20971 X0 X1
       grind)
    | exact resolve eq20971 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20971
  have eq21089 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21066 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq21066
    | (have j0 := eq21066 X0 X1
       grind)
    | exact resolve eq21066 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21066
  have eq21097 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21089 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq21089
    | (have j0 := eq21089 X0 X1
       grind)
    | exact resolve eq21089 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21089
  have eq23208 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq21097 y x
       grind)
    | exact superpose eq21097 eq14
    | (have j1 := eq21097 y x
       grind)
    | exact resolve eq14 eq21097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21097
  have eq23566 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq23208
       have i₂ := eq7042 x y
       grind)
    | exact superpose eq7042 eq23208
    | (have j1 := eq7042 x y
       grind)
    | (have r₁ := eq23208
       have r₂ := eq7042 x y
       grind)
    | exact resolve eq23208 eq7042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7042 eq23208
  have eq23567 : y = (k y x) ∨ y = (M.op y x) := by grind
  clear eq23566
  have eq23570 : y = (k y x) := by
    first
    | (have j1 := eq11455 y x
       grind)
    | (have r₁ := eq23567
       have r₂ := eq11455 y x
       grind)
    | exact resolve eq23567 eq11455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11455 eq23567
  have eq23728 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq23570
       grind)
    | exact superpose eq23570 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq23570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25141 : ∀ X0 X1 : G, (M.op y X0) = (M.op y X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq17 y x x x
       have i₂ := eq23728
       grind)
    | exact superpose eq23728 eq17
    | exact resolve eq17 eq23728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq28477 : ∀ X0 : G, y = (M.op y X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq23728
       have i₂ := eq25141 x X0
       grind)
    | (have i₁ := eq23728
       have i₂ := eq25141 X0 x
       grind)
    | exact superpose eq25141 eq23728
    | exact resolve eq23728 eq25141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23728 eq25141
  have eq28637 : ∀ X0 : G, y = (M.op y X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq28477 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28477
  have eq29525 : ∀ X1 : G, y = (M.op X1 y) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq24 y X1 x
       have i₂ := eq28637 (M.op X1 y)
       grind)
    | exact superpose eq28637 eq24
    | exact resolve eq24 eq28637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28637
  have eq30711 : ∀ X0 X1 : G, (k X0 (M.op y x)) = X0 ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq273 y x X0
       have i₂ := eq29525 X1
       grind)
    | exact superpose eq29525 eq273
    | (have j1 := eq29525 X1
       grind)
    | exact resolve eq273 eq29525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273 eq29525
  have eq33017 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X1)) X2) ∨ (M.op (σ (τ X1)) X2) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12223 (τ X0) (τ X1) X2
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq12223
    | (have j0 := eq12223 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq12223 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12223
  have eq33131 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X1)) X2) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33017 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq33017
    | (have j0 := eq33017 X0 X1 X2
       grind)
    | exact resolve eq33017 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33017
  have eq33155 : ∀ X0 X1 X2 : G, (k X0 X1) ≠ (M.op X1 X2) ∨ (M.op (σ (τ X1)) X2) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33131 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq33131
    | (have j0 := eq33131 X0 X1 X2
       grind)
    | exact resolve eq33131 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33131
  have eq33168 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33155 X0 X0 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33155
    | (have j0 := eq33155 X0 X1 X2
       grind)
    | exact resolve eq33155 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33155
  have eq33171 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 X2) ∨ (k X0 X1) ≠ (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33168 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33168
    | (have j0 := eq33168 X0 X1 X2
       grind)
    | exact resolve eq33168 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33168
  have eq37931 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X2 (M.op X3 X2)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (M.op X4 (M.op X5 X4)) = (M.op (σ X1) X6) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq111 X2 X3 (σ X0) (σ X1)
       have i₂ := eq661 X1 X4 X5 X0 X6
       grind)
    | exact superpose eq661 eq111
    | (have j1 := eq661 X1 X2 X3 X3 (σ (k X0 X1))
       grind)
    | exact resolve eq111 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq46960 : ∀ X2 X3 : G, y = (k y X2) ∨ (k X3 (M.op y x)) = X3 := by
    intro X2 X3
    first
    | (have i₁ := eq11651 x x y X3
       have i₂ := eq30711 x (M.op x x)
       grind)
    | exact superpose eq30711 eq11651
    | (have j1 := eq30711 X3 x
       grind)
    | exact resolve eq11651 eq30711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30711
  have eq81188 : y ≠ y ∨ y = (k y (M.op y x)) := by
    first
    | (have j0 := eq46960 (M.op y x) y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46960
  have eq81189 : y = (k y (M.op y x)) := by grind
  clear eq81188
  have eq81742 : y ≠ y ∨ (M.op y x) = (k (M.op y x) y) := by
    first
    | (have i₁ := eq15673 y (M.op y x)
       have i₂ := eq81189
       grind)
    | exact superpose eq81189 eq15673
    | (have j0 := eq15673 y (M.op y x)
       grind)
    | (have r₁ := eq15673 y (M.op y x)
       have r₂ := eq81189
       grind)
    | exact resolve eq15673 eq81189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15673 eq81189
  have eq81748 : (M.op y x) = (k (M.op y x) y) := by grind
  clear eq81742
  have eq82733 : (M.op y x) = (M.op (M.op y x) y) ∨ (M.op y x) = (k (M.op y x) y) := by
    first
    | (have i₁ := eq81748
       have i₂ := eq11111 y (M.op y x)
       grind)
    | exact superpose eq11111 eq81748
    | (have j1 := eq11111 y (M.op y x)
       grind)
    | exact resolve eq81748 eq11111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11111 eq81748
  have eq82767 : (M.op y x) = (M.op (M.op y x) y) := by
    first
    | (have j1 := eq33171 (M.op y x) y x
       grind)
    | (have r₁ := eq82733
       have r₂ := eq33171 (M.op y x) y x
       grind)
    | exact resolve eq82733 eq33171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33171 eq82733
  have eq82768 : (M.op y x) = (M.op x (M.op y x)) := by
    first
    | (have i₁ := eq82767
       have i₂ := eq8 x y y
       grind)
    | exact superpose eq8 eq82767
    | exact resolve eq82767 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82767
  have eq83774 : ∀ X0 : G, (M.op y x) = (M.op X0 (M.op y x)) := by
    intro X0
    first
    | (have i₁ := eq24 x y x
       have i₂ := eq82768
       grind)
    | exact superpose eq82768 eq24
    | exact resolve eq24 eq82768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq83777 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq111 X0 X1 y x
       have i₂ := eq82768
       grind)
    | exact superpose eq82768 eq111
    | exact resolve eq111 eq82768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq82768
  have eq86907 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X3) = (M.op y x) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq210 X0 X1 x (M.op y x) X3
       have i₂ := eq83774 (M.op (M.op X0 X1) x)
       grind)
    | exact superpose eq83774 eq210
    | exact resolve eq210 eq83774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq83774
  have eq95140 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X4 X3)) ≠ (M.op (σ X0) X2) ∨ (M.op X3 (M.op X4 X3)) = (M.op (σ X0) (σ (k X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq10348 X1 X0 X3 X4 X4 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10348
  have eq95142 : ∀ X0 X1 X3 X4 : G, (M.op X3 (M.op X4 X3)) = (M.op (σ X0) (σ (k X1 X0))) := by
    intro X0 X1 X3 X4
    first
    | (have j0 := eq95140 X0 X1 x X3 X4
       have j1 := eq37931 X1 X0 X3 X4 X3 X4 (σ (k X1 X0))
       grind)
    | (have r₁ := eq95140 X1 X1 (σ (k X0 X1)) x X3
       have r₂ := eq37931 X0 X1 x X3 X4 x x
       grind)
    | (have r₁ := eq95140 X1 X1 x X4 x
       have r₂ := eq37931 X0 X1 x X3 X4 x x
       grind)
    | (have r₁ := eq95140 X0 X1 (M.op x (σ X0)) (σ X1) X4
       have r₂ := eq37931 X0 X1 x X3 (σ X0) x (M.op X4 (σ X1))
       grind)
    | exact resolve eq95140 eq37931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37931 eq95140
  have eq95916 : ∀ X0 X1 : G, (M.op (σ X0) (σ (k X1 X0))) = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq95142 X0 X1 x x
       have i₂ := eq83777 x x
       grind)
    | exact superpose eq83777 eq95142
    | exact resolve eq95142 eq83777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95142
  have eq109053 : ∀ X0 X1 : G, (M.op (σ (τ X1)) (σ (τ (k X0 X1)))) = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq95916 (τ X1) (τ X0)
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq95916
    | exact resolve eq95916 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq109066 : (M.op (σ x) (σ y)) = (M.op y x) := by
    first
    | (have i₁ := eq95916 x y
       have i₂ := eq23570
       grind)
    | exact superpose eq23570 eq95916
    | exact resolve eq95916 eq23570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95916
  have eq109407 : ∀ X0 X1 : G, (M.op (σ (τ X1)) (k X0 X1)) = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq109053 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq109053
    | exact resolve eq109053 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109053
  have eq109452 : ∀ X0 X1 : G, (M.op X1 (k X0 X1)) = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq109407 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq109407
    | exact resolve eq109407 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109407
  have eq110225 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X1 (M.op X2 X1))) X0) = (M.op y x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq109452 X0 (σ (M.op X1 (M.op X2 X1)))
       have i₂ := eq329 X0 X1 X2
       grind)
    | exact superpose eq329 eq109452
    | exact resolve eq109452 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq110261 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X1) X2)) = (M.op y x) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq109452 (M.op (M.op X0 X1) X2) X3
       have i₂ := eq11651 X0 X1 X2 X3
       grind)
    | exact superpose eq11651 eq109452
    | exact resolve eq109452 eq11651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11651
  have eq110295 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq109452 y x
       have i₂ := eq23570
       grind)
    | exact superpose eq23570 eq109452
    | exact resolve eq109452 eq23570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23570 eq109452
  have eq110769 : ∀ X0 X1 X2 X3 : G, (M.op x y) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq110261 X0 X1 X2 X3
       have i₂ := eq110295
       grind)
    | exact superpose eq110295 eq110261
    | exact resolve eq110261 eq110295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110261
  have eq110797 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (σ (M.op X1 (M.op X2 X1))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq110225 X0 X1 X2
       have i₂ := eq110295
       grind)
    | exact superpose eq110295 eq110225
    | exact resolve eq110225 eq110295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110225
  have eq110803 : ∀ X3 : G, (M.op x y) = (M.op X3 (M.op y x)) := by
    intro X3
    first
    | (have i₁ := eq110769 x x x X3
       have i₂ := eq86907 x x x
       grind)
    | exact superpose eq86907 eq110769
    | exact resolve eq110769 eq86907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86907 eq110769
  have eq110823 : ∀ X0 : G, (M.op x y) = (M.op (σ (M.op y x)) X0) := by
    intro X0
    first
    | (have i₁ := eq110797 X0 x x
       have i₂ := eq83777 x x
       grind)
    | exact superpose eq83777 eq110797
    | exact resolve eq110797 eq83777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83777 eq110797
  have eq110827 : ∀ X3 : G, (M.op x y) = (M.op X3 (M.op x y)) := by
    intro X3
    first
    | (have i₁ := eq110803 X3
       have i₂ := eq110295
       grind)
    | exact superpose eq110295 eq110803
    | exact resolve eq110803 eq110295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110803
  have eq110847 : ∀ X0 : G, (M.op x y) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq110823 X0
       have i₂ := eq110295
       grind)
    | exact superpose eq110295 eq110823
    | exact resolve eq110823 eq110295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110823
  have eq114754 : (σ (M.op x y)) ≠ (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq109066
       grind)
    | exact superpose eq109066 eq14
    | exact resolve eq14 eq109066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109066
  have eq114971 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq114754
       have i₂ := eq110295
       grind)
    | exact superpose eq110295 eq114754
    | exact resolve eq114754 eq110295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110295 eq114754
  have eq119027 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq6931 x x (M.op x y)
       have i₂ := eq110827 (M.op x x)
       grind)
    | exact superpose eq110827 eq6931
    | exact resolve eq6931 eq110827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6931 eq110827
  have eq119207 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq119027
       have i₂ := eq110847 (σ (M.op x y))
       grind)
    | exact superpose eq110847 eq119027
    | exact resolve eq119027 eq110847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110847 eq119027
  have eq119256 : False := by grind
  exact eq119256
