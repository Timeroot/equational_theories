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

/-- `Equation3744`: `x ◇ y = (x ◇ z) ◇ (w ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_y_x_pyx_Equation3744 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3744 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3744.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq17 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq8 (M.op X0 X2) X3 (M.op x X1) X5
       have i₂ := eq8 X0 X1 X2 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X2 (M.op X3 X1) X4 (M.op X0 x)
       have i₂ := eq8 X0 X1 x X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq18 x X1 X2 X3 x
       have i₂ := eq8 X2 X1 x x
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq21 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq17 X0 x X2 X3 x
       have i₂ := eq8 X0 X3 x x
       grind)
    | exact superpose eq8 eq17
    | exact resolve eq17 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq33 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq54 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq60 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k X0 (τ X1)) X2
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq13
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq54
    | exact resolve eq54 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq111 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq33 X0 X1
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq33 X0 X1
       grind)
    | exact resolve eq11 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 X2 : G, (M.op (σ X1) X2) = (M.op (σ X0) X2) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (σ X1) (σ X0) X2
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq21
    | (have j1 := eq33 X0 X1
       grind)
    | exact resolve eq21 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq115 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq33 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq111 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq117 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq116 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq116
    | (have j0 := eq116 X0 X1
       grind)
    | exact resolve eq116 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq645 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq117 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq117
    | exact resolve eq117 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq645 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq645
    | (have j0 := eq645 X0 X1
       grind)
    | exact resolve eq645 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq686 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq682 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq682
    | (have j0 := eq682 X0 X1
       grind)
    | exact resolve eq682 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq682
  have eq1011 : ∀ X0 X1 X2 : G, (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X2)) ∨ (σ X1) = (σ (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq117 X2 X1
       have i₂ := eq114 X2 X0 (σ X1)
       grind)
    | (have i₁ := eq117 X1 X1
       have i₂ := eq114 X0 X1 (σ X1)
       grind)
    | exact superpose eq114 eq117
    | (have j0 := eq117 X2 X0
       have j1 := eq114 X2 X0 X2
       grind)
    | exact resolve eq117 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq1058 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq3204 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq686 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq686
    | exact resolve eq686 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq12361 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1058 (τ X0) (τ X1)
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq1058
    | exact resolve eq1058 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq1058
  have eq12473 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op X0 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12361 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12361
    | (have j0 := eq12361 X0 X1
       grind)
    | exact resolve eq12361 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12361
  have eq12506 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12473 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq12473
    | (have j0 := eq12473 X0 X1
       grind)
    | exact resolve eq12473 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12473
  have eq12527 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12506 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12506
    | (have j0 := eq12506 X0 X1
       grind)
    | exact resolve eq12506 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12506
  have eq12533 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12527 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq12527
    | (have j0 := eq12527 X0 X1
       grind)
    | exact resolve eq12527 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12527
  have eq12534 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12533 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq12533
    | (have j0 := eq12533 X0 X1
       grind)
    | exact resolve eq12533 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12533
  have eq65100 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq115 X1
       have i₂ := eq1011 X0 X1 X1
       grind)
    | exact superpose eq1011 eq115
    | (have j0 := eq115 X1
       have j1 := eq1011 X0 X1 X1
       grind)
    | (have r₁ := eq115 x
       have r₂ := eq1011 X0 x x
       grind)
    | exact resolve eq115 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq65501 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq65100 X0 X1
       have j1 := eq115 X1
       grind)
    | (have r₁ := eq65100 X0 X0
       have r₂ := eq115 X0
       grind)
    | (have r₁ := eq65100 X0 X0
       have r₂ := eq115 X0
       grind)
    | exact resolve eq65100 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq65100
  have eq65882 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq65501 X0 X1
       have j1 := eq33 X1 X0
       grind)
    | (have r₁ := eq65501 X1 X0
       have r₂ := eq33 X0 X1
       grind)
    | exact resolve eq65501 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq65501
  have eq259487 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (k (M.op X0 X1) X2) ∨ (M.op X2 (M.op X0 X1)) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12534 (M.op X0 X1) X2
       have i₂ := eq8 X0 X1 X1 X0
       grind)
    | exact superpose eq8 eq12534
    | (have j0 := eq12534 (M.op X0 X1) X2
       grind)
    | exact resolve eq12534 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12534
  have eq259496 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq259487 X0 X1 X2
       have j1 := eq3204 X2 (M.op X0 X1)
       grind)
    | (have r₁ := eq259487 X0 X1 X0
       have r₂ := eq3204 X0 (M.op X0 X1)
       grind)
    | exact resolve eq259487 eq3204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3204 eq259487
  have eq259555 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq259496 X0 X1 X2
       have i₂ := eq20 X1 X2 X0
       grind)
    | exact superpose eq20 eq259496
    | exact resolve eq259496 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq259496
  have eq284444 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq65882 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq65882
    | exact resolve eq65882 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65882
  have eq284523 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq284444 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq284444
    | (have j0 := eq284444 X0 X1
       grind)
    | exact resolve eq284444 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq284444
  have eq284538 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq284523 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq284523
    | (have j0 := eq284523 X1 X1
       grind)
    | exact resolve eq284523 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284523
  have eq285202 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq259555 X0 X0 X1
       have i₂ := eq284538 X2 X0
       grind)
    | exact superpose eq284538 eq259555
    | (have j1 := eq284538 X0 X1
       grind)
    | exact resolve eq259555 eq284538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284538
  have eq288960 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X0) = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq285202 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285202
  have eq288961 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq288960 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288960
  have eq289404 : ∀ X0 X1 : G, (k (M.op (σ X0) (σ X0)) (σ X1)) = (σ (k (k X0 (τ (σ X0))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 (σ X0) X1
       have i₂ := eq288961 (σ X0)
       grind)
    | exact superpose eq288961 eq60
    | exact resolve eq60 eq288961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq289538 : ∀ X0 X1 : G, (σ (k (k X0 X0) X1)) = (k (M.op (σ X0) (σ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq289404 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq289404
    | exact resolve eq289404 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289404
  have eq289582 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq289538 X0 X1
       have i₂ := eq259555 (σ X0) (σ X0) (σ X1)
       grind)
    | exact superpose eq259555 eq289538
    | exact resolve eq289538 eq259555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289538
  have eq289601 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq289582 X0 X1
       have i₂ := eq288961 X0
       grind)
    | exact superpose eq288961 eq289582
    | exact resolve eq289582 eq288961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288961 eq289582
  have eq289612 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq289601 X0 X1
       have i₂ := eq259555 X0 X0 X1
       grind)
    | exact superpose eq259555 eq289601
    | exact resolve eq289601 eq259555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259555 eq289601
  have eq295822 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq289612 y x
       grind)
    | exact superpose eq289612 eq14
    | (have r₁ := eq14
       have r₂ := eq289612 y x
       grind)
    | exact resolve eq14 eq289612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289612
  have eq296004 : False := by grind
  exact eq296004

/-- `Equation3748`: `x ◇ y = (y ◇ x) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation3748 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3748 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3748.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X0 X0)) := by
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
  have eq18 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X0 X0) (M.op X1 X0)
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X0 X0) X1
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq8 X0 X0
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
  have eq31 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X2 X1) X0) ∨ (M.op X0 X1) = (k X1 X0) := by
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
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq43 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq52 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq32
    | exact resolve eq32 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq32 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq98 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq33 (σ X0) (σ X1)
       grind)
    | exact superpose eq33 eq13
    | (have j1 := eq33 (σ X0) X1
       grind)
    | exact resolve eq13 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq33 X0 (τ X1)
       grind)
    | exact superpose eq33 eq16
    | (have j1 := eq33 X0 X1
       grind)
    | exact resolve eq16 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq43
  have eq122 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq107 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq107
    | exact resolve eq107 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq143 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X0 X0) (M.op X1 X0))) = (M.op (M.op X0 X1) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq21
    | exact resolve eq21 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X1)) = (M.op (M.op X1 X2) X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq21 X0 X1
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq21
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op (M.op (M.op X0 X0) (M.op X1 X0)) X2) ∨ (M.op X2 (M.op X0 X0)) = (k (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X2 (M.op X0 X0) (M.op X0 X1)
       have i₂ := eq21 X0 X1
       grind)
    | (have i₁ := eq31 X0 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq31
    | (have j0 := eq31 X2 (M.op X0 X0) X2
       grind)
    | exact resolve eq31 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq31
  have eq358 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq35 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq35
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq9
    | (have j1 := eq35 X1 X0
       grind)
    | exact resolve eq9 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (M.op (σ X0) (σ X0)) (σ X2)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq13
    | (have j1 := eq35 X1 X0
       grind)
    | exact resolve eq13 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq35 X2 X0
       grind)
    | exact superpose eq35 eq13
    | (have j1 := eq35 X2 X0
       grind)
    | exact resolve eq13 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq409 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq35 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq974 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq99 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq99
    | (have j0 := eq99 X1 X1
       grind)
    | exact resolve eq99 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq1038 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq974 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq974
    | (have j0 := eq974 X0 X1
       grind)
    | exact resolve eq974 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974
  have eq1094 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 X0
       have i₂ := eq1038 X1 X0
       grind)
    | exact superpose eq1038 eq68
    | (have j0 := eq68 X0 X0
       have j1 := eq1038 X1 X0
       grind)
    | (have r₁ := eq68 X1 X1
       have r₂ := eq1038 X0 X1
       grind)
    | exact resolve eq68 eq1038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1038
  have eq1103 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1094 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094
  have eq1254 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq409 X0
       have i₂ := eq1103 X0 X1
       grind)
    | exact superpose eq1103 eq409
    | (have j0 := eq409 X0
       have j1 := eq1103 X0 X1
       grind)
    | exact resolve eq409 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409 eq1103
  have eq1281 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1254 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254
  have eq1936 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq61 X0 X0
       grind)
    | exact superpose eq61 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq61 X0 X0
       grind)
    | exact resolve eq12 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq2749 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq98 x y
       grind)
    | exact superpose eq98 eq14
    | (have j1 := eq98 x x
       grind)
    | exact resolve eq14 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq2804 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq1281 x x
       grind)
    | (have r₁ := eq2749
       have r₂ := eq1281 x y
       grind)
    | exact resolve eq2749 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281 eq2749
  have eq2820 : x = (k x (τ (σ x))) := by
    first
    | (have i₁ := eq122 x
       have i₂ := eq2804
       grind)
    | exact superpose eq2804 eq122
    | exact resolve eq122 eq2804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq2842 : x = (k x x) := by
    first
    | (have i₁ := eq2820
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq2820
    | exact resolve eq2820 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2820
  have eq2950 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq33 x x
       have i₂ := eq2842
       grind)
    | exact superpose eq2842 eq33
    | (have j0 := eq33 x x
       grind)
    | exact resolve eq33 eq2842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq2842
  have eq2954 : x = (M.op x x) := by grind
  clear eq2950
  have eq3018 : ∀ X0 : G, (M.op x X0) = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | (have i₁ := eq19 x x
       have i₂ := eq2954
       grind)
    | exact superpose eq2954 eq19
    | exact resolve eq19 eq2954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3283 : ∀ X0 : G, (τ (σ x)) = X0 ∨ (M.op (σ X0) (σ x)) = (σ (k x X0)) := by
    intro X0
    first
    | (have i₁ := eq385 x X0
       have i₂ := eq2804
       grind)
    | exact superpose eq2804 eq385
    | (have j0 := eq385 x X0
       grind)
    | exact resolve eq385 eq2804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq3381 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (k x X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq3283 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq3283
    | (have j0 := eq3283 X0
       grind)
    | exact resolve eq3283 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3283
  have eq8831 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (k X1 X2)) = (k (M.op X0 X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq386 (τ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq386
    | exact resolve eq386 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq9007 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k X1 X2)) = (k (M.op X0 X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8831 X0 X1 X2
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq8831
    | (have j0 := eq8831 X0 X1 X2
       grind)
    | exact resolve eq8831 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8831
  have eq9357 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (k X2 X1)) = (k (σ X2) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq387 (τ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq387
    | exact resolve eq387 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq9534 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k X2 X1)) = (k (σ X2) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9357 X0 X1 X2
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9357
    | (have j0 := eq9357 X0 X1 X2
       grind)
    | exact resolve eq9357 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9357
  have eq20020 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X1) X0) ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq143 X0 X0
       have i₂ := eq12 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq143 X0 X1
       have i₂ := eq12 X0 (M.op (M.op X0 X0) (M.op X1 X0))
       grind)
    | exact superpose eq12 eq143
    | (have j1 := eq12 X0 (M.op (M.op X1 X1) X0)
       grind)
    | exact resolve eq143 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq26463 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op X2 (M.op (M.op X1 X0) (M.op X0 X0))) ∨ (M.op X2 (M.op X0 X0)) = (k (M.op X0 X0) X2) ∨ (M.op X2 (M.op X0 X0)) = (k (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq148 X2 (M.op X0 X0) (M.op X1 X0)
       have i₂ := eq187 X0 X1 X2
       grind)
    | exact superpose eq187 eq148
    | (have j0 := eq148 X2 (M.op X0 X0) X2
       have j1 := eq187 X0 X1 X2
       grind)
    | exact resolve eq148 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq187
  have eq26588 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op X2 (M.op (M.op X1 X0) (M.op X0 X0))) ∨ (M.op X2 (M.op X0 X0)) = (k (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq26463 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26463
  have eq26647 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op X2 (M.op X0 X1)) ∨ (M.op X2 (M.op X0 X0)) = (k (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26588 X0 X1 X2
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq26588
    | (have j0 := eq26588 X0 X1 X2
       grind)
    | exact resolve eq26588 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26588
  have eq59050 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (M.op X2 X2) (σ (τ X1))) ∨ (k X2 (σ (τ X0))) = (M.op (σ (τ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9007 X2 (τ X0) (τ X1)
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq9007
    | (have j0 := eq9007 X2 (τ X0) X2
       grind)
    | exact resolve eq9007 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9007
  have eq59085 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (M.op X2 X2) X1) ∨ (k X2 (σ (τ X0))) = (M.op (σ (τ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59050 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq59050
    | (have j0 := eq59050 X0 X1 X2
       grind)
    | exact resolve eq59050 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59050
  have eq59091 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (M.op X2 X2) X1) ∨ (k X2 (σ (τ X0))) = (M.op (σ (τ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59085 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq59085
    | (have j0 := eq59085 X0 X1 X2
       grind)
    | exact resolve eq59085 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59085
  have eq59092 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (k X0 X1) = (k (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59091 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq59091
    | (have j0 := eq59091 X0 X1 X2
       grind)
    | exact resolve eq59091 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59091
  have eq59175 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (σ (τ X0)) (M.op X2 X2)) ∨ (k X2 (σ (τ X1))) = (M.op (σ (τ X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9534 X2 (τ X1) (τ X0)
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq9534
    | (have j0 := eq9534 X2 (τ X1) X2
       grind)
    | exact resolve eq9534 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq9534
  have eq59218 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k X0 (M.op X2 X2)) ∨ (k X2 (σ (τ X1))) = (M.op (σ (τ X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59175 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq59175
    | (have j0 := eq59175 X0 X1 X2
       grind)
    | exact resolve eq59175 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59175
  have eq59224 : ∀ X0 X1 X2 : G, (k X0 X1) = (k X0 (M.op X2 X2)) ∨ (k X2 (σ (τ X1))) = (M.op (σ (τ X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59218 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq59218
    | (have j0 := eq59218 X0 X1 X2
       grind)
    | exact resolve eq59218 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59218
  have eq59225 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k X2 X1) ∨ (k X0 X1) = (k X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59224 X0 X0 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq59224
    | (have j0 := eq59224 X0 X1 X2
       grind)
    | exact resolve eq59224 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59224
  have eq59389 : ∀ X0 : G, (k x X0) = (M.op X0 x) ∨ (M.op X0 X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq20020 X0 x
       have i₂ := eq2954
       grind)
    | exact superpose eq2954 eq20020
    | exact resolve eq20020 eq2954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20020
  have eq59710 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 x) ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 x
       have i₂ := eq59389 X0
       grind)
    | (have i₁ := eq8 X0 X0
       have i₂ := eq59389 X0
       grind)
    | exact superpose eq59389 eq8
    | (have j1 := eq59389 X0
       grind)
    | exact resolve eq8 eq59389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59389
  have eq59725 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 x) ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq59710 X0
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq59710
    | (have j0 := eq59710 X0
       grind)
    | exact resolve eq59710 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59710
  have eq59867 : ∀ X0 X1 : G, (M.op X0 x) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (k x X0) = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq59725 X0
       grind)
    | (have i₁ := eq12 x X1
       have i₂ := eq59725 x
       grind)
    | exact superpose eq59725 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq59725 X0
       grind)
    | exact resolve eq12 eq59725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64761 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1936 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1936
  have eq64762 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq64761 X0 X1
       have j1 := eq358 X1 X0
       grind)
    | (have r₁ := eq64761 (k X1 X1) X0
       have r₂ := eq358 X0 X1
       grind)
    | (have r₁ := eq64761 X0 (σ (k X1 X1))
       have r₂ := eq358 (σ X0) X1
       grind)
    | (have r₁ := eq64761 X1 X0
       have r₂ := eq358 X0 X1
       grind)
    | exact resolve eq64761 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358 eq64761
  have eq64831 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq64762 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq64762 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq64762 eq16
    | (have j1 := eq64762 (τ X1) X0
       grind)
    | exact resolve eq16 eq64762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq64762
  have eq64872 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq64831 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq64831
    | (have j0 := eq64831 X0 X1
       grind)
    | exact resolve eq64831 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64831
  have eq64884 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq64872 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq64872
    | (have j0 := eq64872 X0 X1
       grind)
    | exact resolve eq64872 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64872
  have eq76962 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X1) = (k (M.op X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26647 X0 X0 (M.op X1 X0)
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq26647
    | exact resolve eq26647 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26647
  have eq76969 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k (M.op X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76962 X0 X1
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq76962
    | (have j0 := eq76962 X0 X1
       grind)
    | exact resolve eq76962 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76962
  have eq84124 : ∀ X0 X1 : G, (k X0 X1) = (k x X1) ∨ (k x X0) = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq59092 X0 X1 x
       have i₂ := eq2954
       grind)
    | exact superpose eq2954 eq59092
    | (have j0 := eq59092 X0 X1 x
       grind)
    | exact resolve eq59092 eq2954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59092
  have eq84874 : ∀ X0 : G, (k X0 X0) ≠ (M.op X0 x) ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq84124 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84124
  have eq85414 : ∀ X0 X1 : G, (M.op X1 x) ≠ X0 ∨ (M.op X1 x) = (k x X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq84874 X1
       have i₂ := eq64884 X0 X1
       grind)
    | (have i₁ := eq84874 X0
       have i₂ := eq64884 (k X0 X0) X1
       grind)
    | exact superpose eq64884 eq84874
    | (have j0 := eq84874 X1
       have j1 := eq64884 X1 x
       grind)
    | (have r₁ := eq84874 x
       have r₂ := eq64884 x x
       grind)
    | (have r₁ := eq84874 X1
       have r₂ := eq64884 (M.op X1 x) X1
       grind)
    | exact resolve eq84874 eq64884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64884
  have eq85487 : ∀ X0 X1 : G, (M.op X1 x) = (k x X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq85414 X0 X1
       have j1 := eq59867 X1 (k x X1)
       grind)
    | (have r₁ := eq85414 X1 X0
       have r₂ := eq59867 X0 X1
       grind)
    | (have r₁ := eq85414 (M.op X0 x) X1
       have r₂ := eq59867 X0 (M.op X1 x)
       grind)
    | (have r₁ := eq85414 (k x X1) X1
       have r₂ := eq59867 x X1
       grind)
    | exact resolve eq85414 eq59867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59867 eq85414
  have eq86454 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 x) ∨ (k x X0) = (M.op X0 x) ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq84874 X0
       have i₂ := eq85487 X0 X0
       grind)
    | exact superpose eq85487 eq84874
    | (have j0 := eq84874 X0
       have j1 := eq85487 X0 X0
       grind)
    | (have r₁ := eq84874 x
       have r₂ := eq85487 X0 x
       grind)
    | (have r₁ := eq84874 x
       have r₂ := eq85487 x x
       grind)
    | exact resolve eq84874 eq85487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84874 eq85487
  have eq86587 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 x) ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq86454 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86454
  have eq86611 : ∀ X0 : G, (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq86587 X0
       have j1 := eq59725 X0
       grind)
    | (have r₁ := eq86587 X0
       have r₂ := eq59725 X0
       grind)
    | (have r₁ := eq86587 x
       have r₂ := eq59725 x
       grind)
    | exact resolve eq86587 eq59725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59725 eq86587
  have eq93888 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 (M.op X0 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq59225 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59225
  have eq93889 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  clear eq93888
  have eq93972 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k (M.op X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq93889 (M.op X0 X0) (M.op X1 X0)
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq93889
    | (have r₁ := eq93889 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq8 X1 X1
       grind)
    | exact resolve eq93889 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93889
  have eq94131 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq93972 X0 X1
       have j1 := eq76969 X0 X1
       grind)
    | (have r₁ := eq93972 X0 X1
       have r₂ := eq76969 X0 X1
       grind)
    | (have r₁ := eq93972 X1 X1
       have r₂ := eq76969 X1 X1
       grind)
    | exact resolve eq93972 eq76969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76969 eq93972
  have eq94278 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (k (M.op (σ x) (σ x)) (σ (k x X0))) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq94131 (σ x) (σ X0)
       have i₂ := eq3381 X0
       grind)
    | exact superpose eq3381 eq94131
    | (have j1 := eq3381 X0
       grind)
    | exact resolve eq94131 eq3381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3381 eq94131
  have eq94404 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (k (M.op (σ x) (σ x)) (σ (M.op X0 x))) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq94278 X0
       have i₂ := eq86611 X0
       grind)
    | exact superpose eq86611 eq94278
    | (have j0 := eq94278 X0
       grind)
    | exact resolve eq94278 eq86611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94278
  have eq94453 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (k (σ x) (σ (M.op X0 x))) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq94404 X0
       have i₂ := eq2804
       grind)
    | exact superpose eq2804 eq94404
    | (have j0 := eq94404 X0
       grind)
    | exact resolve eq94404 eq2804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94404
  have eq94477 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k x (M.op X0 x))) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq94453 X0
       have i₂ := eq13 x (M.op X0 x)
       grind)
    | exact superpose eq13 eq94453
    | (have j0 := eq94453 X0
       grind)
    | exact resolve eq94453 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94453
  have eq94486 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op (M.op X0 x) x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq94477 X0
       have i₂ := eq86611 (M.op X0 x)
       grind)
    | exact superpose eq86611 eq94477
    | (have j0 := eq94477 X0
       grind)
    | exact resolve eq94477 eq86611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86611 eq94477
  have eq94489 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq94486 X0
       have i₂ := eq3018 X0
       grind)
    | exact superpose eq3018 eq94486
    | (have j0 := eq94486 X0
       grind)
    | exact resolve eq94486 eq3018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3018 eq94486
  have eq95047 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq94489 y
       grind)
    | exact superpose eq94489 eq14
    | (have j1 := eq94489 y
       grind)
    | (have r₁ := eq14
       have r₂ := eq94489 y
       grind)
    | exact resolve eq14 eq94489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94489
  have eq95070 : x = y := by grind
  clear eq95047
  have eq95079 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq95070
       grind)
    | exact superpose eq95070 eq14
    | exact resolve eq14 eq95070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95070
  have eq95225 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq95079
       have i₂ := eq2954
       grind)
    | exact superpose eq2954 eq95079
    | exact resolve eq95079 eq2954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2954 eq95079
  have eq95226 : False := by grind
  exact eq95226

/-- `Equation3751`: `x ◇ y = (y ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation3751 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3751 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3751.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq30 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq35 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op X0 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 (M.op X0 X1) X2
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq84 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq118 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq30 X1 (τ X0)
       grind)
    | exact superpose eq30 eq16
    | (have j1 := eq30 X1 X1
       grind)
    | exact resolve eq16 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq124 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq40
  have eq139 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq124 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq124
    | exact resolve eq124 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq234 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq32 x y
       grind)
    | exact superpose eq32 eq14
    | (have j1 := eq32 x y
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq9
    | (have j1 := eq32 X0 X1
       grind)
    | exact resolve eq9 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq32 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq888 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq118 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq118
    | (have j0 := eq118 X0 X1
       grind)
    | exact resolve eq118 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq953 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq888 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq888
    | (have j0 := eq888 X0 X1
       grind)
    | exact resolve eq888 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq1124 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq35
    | exact resolve eq35 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1212 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1124 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1124
    | (have j0 := eq1124 X0 X1
       grind)
    | exact resolve eq1124 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq2165 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq234
       have i₂ := eq1212 y x
       grind)
    | exact superpose eq1212 eq234
    | (have j1 := eq1212 (σ y) (σ x)
       grind)
    | (have r₁ := eq234
       have r₂ := eq1212 y x
       grind)
    | exact resolve eq234 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq2166 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq234
       have i₂ := eq953 x y
       grind)
    | exact superpose eq953 eq234
    | (have j1 := eq953 x y
       grind)
    | (have r₁ := eq234
       have r₂ := eq953 x y
       grind)
    | exact resolve eq234 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq2167 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq2166
  have eq2168 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2165
  have eq2194 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq50 (σ x) (σ x)
       have i₂ := eq2167
       grind)
    | exact superpose eq2167 eq50
    | exact resolve eq50 eq2167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq2167
  have eq2200 : (σ y) = (σ (k y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2194
       have i₂ := eq13 y y
       grind)
    | exact superpose eq13 eq2194
    | exact resolve eq2194 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2194
  have eq3024 : (k y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq2200
       grind)
    | exact superpose eq2200 eq9
    | exact resolve eq9 eq2200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2200
  have eq3072 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3024
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3024
    | exact resolve eq3024 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3024
  have eq3073 : y = (k y y) := by
    first
    | (have j1 := eq84 y y
       grind)
    | (have r₁ := eq3072
       have r₂ := eq84 y y
       grind)
    | exact resolve eq3072 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq3072
  have eq3252 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq264 y
       have i₂ := eq3073
       grind)
    | exact superpose eq3073 eq264
    | (have j0 := eq264 y
       grind)
    | exact resolve eq264 eq3073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq3259 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq30 y y
       have i₂ := eq3073
       grind)
    | exact superpose eq3073 eq30
    | (have j0 := eq30 y x
       grind)
    | exact resolve eq30 eq3073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3073
  have eq3263 : y = (M.op y y) := by grind
  clear eq3259
  have eq3266 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3252
  have eq3351 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq49 y y x
       have i₂ := eq3263
       grind)
    | exact superpose eq3263 eq49
    | (have j0 := eq49 y X0 (k y X0)
       grind)
    | exact resolve eq49 eq3263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq3263
  have eq3557 : ∀ X0 : G, (τ (σ y)) = X0 ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq246 y X0
       have i₂ := eq3266
       grind)
    | exact superpose eq3266 eq246
    | (have j0 := eq246 y X0
       grind)
    | exact resolve eq246 eq3266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq3586 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq3557 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3557
    | (have j0 := eq3557 X0
       grind)
    | exact resolve eq3557 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3557
  have eq5188 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq139 x
       have i₂ := eq2168
       grind)
    | exact superpose eq2168 eq139
    | exact resolve eq139 eq2168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq2168
  have eq5210 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5188
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq5188
    | exact resolve eq5188 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5188
  have eq5426 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq5210
       grind)
    | exact superpose eq5210 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq5210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5210
  have eq5437 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq5426
  have eq5832 : y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18 x y
       have i₂ := eq5437
       grind)
    | exact superpose eq5437 eq18
    | exact resolve eq18 eq5437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq5437
  have eq6258 : x ≠ y ∨ x = (M.op x x) := by grind
  clear eq5832
  have eq15379 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq48 (σ X0) (σ y)
       have i₂ := eq3586 X0
       grind)
    | exact superpose eq3586 eq48
    | (have j1 := eq3586 X0
       grind)
    | exact resolve eq48 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3586
  have eq15827 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq15379 x
       grind)
    | exact superpose eq15379 eq14
    | (have j1 := eq15379 x
       grind)
    | exact resolve eq14 eq15379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15379
  have eq16181 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq15827
       have i₂ := eq3351 x
       grind)
    | exact superpose eq3351 eq15827
    | (have j1 := eq3351 x
       grind)
    | exact resolve eq15827 eq3351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3351
  have eq16190 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq15827
       have i₂ := eq953 y x
       grind)
    | exact superpose eq953 eq15827
    | (have j1 := eq953 x x
       grind)
    | exact resolve eq15827 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953 eq15827
  have eq16195 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = y := by grind
  clear eq16181
  have eq16200 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq16190
       have r₂ := eq6258
       grind)
    | exact resolve eq16190 eq6258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6258 eq16190
  have eq16215 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq16195
       have i₂ := eq48 y x
       grind)
    | (have i₁ := eq16195
       have i₂ := eq48 x y
       grind)
    | exact superpose eq48 eq16195
    | exact resolve eq16195 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16195
  have eq16216 : x = y := by grind
  clear eq16215
  have eq16219 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16200
       have i₂ := eq48 y x
       grind)
    | (have i₁ := eq16200
       have i₂ := eq48 x y
       grind)
    | exact superpose eq48 eq16200
    | exact resolve eq16200 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq16200
  have eq16220 : x = (M.op x x) := by grind
  clear eq16219
  have eq16444 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq16216
       grind)
    | exact superpose eq16216 eq14
    | exact resolve eq14 eq16216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16457 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3266
       have i₂ := eq16216
       grind)
    | exact superpose eq16216 eq3266
    | exact resolve eq3266 eq16216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3266 eq16216
  have eq16479 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16444
       have i₂ := eq16220
       grind)
    | exact superpose eq16220 eq16444
    | exact resolve eq16444 eq16220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16220 eq16444
  have eq16480 : False := by grind
  exact eq16480

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

/-- `Equation4277`: `x ◇ (x ◇ x) = y ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4277 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4277 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4277.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X2)) := by
    intro X0 X1 X2
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
  have eq18 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X4)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq8 x X3 X4
       have i₂ := eq8 x X0 X1
       grind)
    | (have i₁ := eq8 x X1 x
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X2)) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X3 X3)
       have i₂ := eq8 X3 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1 (M.op X1 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq32 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 X3
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq38 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq43 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq57 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq18 X2 X3 X4 (M.op X4 x)
       have i₂ := eq18 X4 x X0 X1
       grind)
    | (have i₁ := eq18 X2 X3 X4 (M.op X4 x)
       have i₂ := eq18 X0 X1 X4 x
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq28
    | exact resolve eq28 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq33
    | exact resolve eq33 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq33 (τ X1) X0
       grind)
    | exact superpose eq33 eq17
    | (have j1 := eq33 (τ X1) X0
       grind)
    | exact resolve eq17 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq33 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 X2 X4 X5 X6 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op X4 (M.op X5 (M.op X5 X6))) := by
    intro X0 X1 X2 X4 X5 X6
    first
    | (have i₁ := eq20 X5 X6 x X4
       have i₂ := eq20 X1 X2 x X0
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (k (M.op X1 (M.op X1 X2)) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2
    grind
  clear eq20
  have eq150 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq43
  have eq164 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq150 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq150
    | exact resolve eq150 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq295 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14
       have i₂ := eq32 (σ y) (σ x) X0 X1
       grind)
    | exact superpose eq32 eq14
    | (have j1 := eq32 (σ y) (σ x) x x
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq305 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq295 X0 X1
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq295
    | (have j0 := eq295 X0 X1
       grind)
    | exact resolve eq295 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq410 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq164 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq164 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq164
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq164 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (k (M.op X2 (M.op X2 X3)) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    grind
  have eq584 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq35 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq35
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq600 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq35 x y
       grind)
    | exact superpose eq35 eq14
    | (have j1 := eq35 x y
       grind)
    | exact resolve eq14 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq619 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq9
    | (have j1 := eq35 X0 X1
       grind)
    | exact resolve eq9 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq647 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq35 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1734 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq647 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq647
    | (have j0 := eq647 (τ X0)
       grind)
    | exact resolve eq647 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1736 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1734 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1734
    | (have j0 := eq1734 X0
       grind)
    | exact resolve eq1734 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734
  have eq1739 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1736 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1736
    | (have j0 := eq1736 X0
       grind)
    | exact resolve eq1736 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1736
  have eq1766 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq38
    | exact resolve eq38 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1862 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1766 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1766
    | (have j0 := eq1766 X0 X1
       grind)
    | exact resolve eq1766 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1766
  have eq1884 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1739 (τ X0)
       have i₂ := eq70 X0 X0
       grind)
    | exact superpose eq70 eq1739
    | (have j0 := eq1739 (τ X0)
       grind)
    | exact resolve eq1739 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq1739
  have eq1886 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq82
    | exact resolve eq82 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq1927 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1886 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1886
    | (have j0 := eq1886 X0 X1
       grind)
    | exact resolve eq1886 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886
  have eq2418 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
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
  clear eq79
  have eq3112 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) ≠ (σ (M.op X0 (M.op X0 X0))) ∨ (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq647 (M.op X0 (M.op X0 X0))
       have i₂ := eq142 X0 X0 X0
       grind)
    | exact superpose eq142 eq647
    | (have j0 := eq647 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq647 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq3121 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq3112 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3112
  have eq3181 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq600
       have i₂ := eq1927 y x
       grind)
    | exact superpose eq1927 eq600
    | (have j1 := eq1927 y x
       grind)
    | (have r₁ := eq600
       have r₂ := eq1927 y x
       grind)
    | exact resolve eq600 eq1927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1927
  have eq3182 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq600
       have i₂ := eq1862 y x
       grind)
    | exact superpose eq1862 eq600
    | (have j1 := eq1862 (σ y) (σ x)
       grind)
    | (have r₁ := eq600
       have r₂ := eq1862 y x
       grind)
    | exact resolve eq600 eq1862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600 eq1862
  have eq3183 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq3182
  have eq3184 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq3181
  have eq3196 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq164 x
       have i₂ := eq3183
       grind)
    | exact superpose eq3183 eq164
    | exact resolve eq164 eq3183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3232 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3196
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3196
    | exact resolve eq3196 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3196
  have eq3312 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq3232
       grind)
    | exact superpose eq3232 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq3232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3232
  have eq3317 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq3312
  have eq4365 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq619 x x
       have i₂ := eq3183
       grind)
    | exact superpose eq3183 eq619
    | exact resolve eq619 eq3183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq4416 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4365
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq4365
    | exact resolve eq4365 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4365
  have eq4732 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq164 x
       have i₂ := eq3184
       grind)
    | exact superpose eq3184 eq164
    | exact resolve eq164 eq3184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq3184
  have eq4778 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq4732
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq4732
    | exact resolve eq4732 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4732
  have eq4779 : x = (k x y) := by grind
  clear eq4778
  have eq4789 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq584 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq584
    | (have j0 := eq584 X1 (τ X0)
       grind)
    | exact resolve eq584 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq4906 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4789 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq4789
    | (have j0 := eq4789 X0 X1
       grind)
    | exact resolve eq4789 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq4789
  have eq4916 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4906 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4906
    | (have j0 := eq4906 X0 X1
       grind)
    | exact resolve eq4906 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4906
  have eq6835 : ∀ X0 X1 X2 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 (M.op X1 X2))) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq305 x (M.op x x)
       have i₂ := eq107 x x x X0 X1 X2
       grind)
    | (have i₁ := eq305 x (M.op x x)
       have i₂ := eq107 X0 X1 X2 x x x
       grind)
    | exact superpose eq107 eq305
    | exact resolve eq305 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq305
  have eq6855 : ∀ X0 X1 X2 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 (M.op X1 X2))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6835 X0 X1 X2
       have i₂ := eq4779
       grind)
    | exact superpose eq4779 eq6835
    | (have j0 := eq6835 X0 X1 X2
       grind)
    | exact resolve eq6835 eq4779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4779 eq6835
  have eq23352 : ∀ X0 : G, (τ (σ X0)) ≠ (τ (M.op (σ X0) (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1884 (σ X0)
       have i₂ := eq410 (σ X0) X0
       grind)
    | exact superpose eq410 eq1884
    | (have j0 := eq1884 (σ X0)
       have j1 := eq410 (σ X0) X0
       grind)
    | exact resolve eq1884 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq1884
  have eq23382 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq23352 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq23352
    | (have j0 := eq23352 X0
       grind)
    | exact resolve eq23352 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23352
  have eq23393 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq23382 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq23382
    | (have j0 := eq23382 X0
       grind)
    | exact resolve eq23382 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23382
  have eq23397 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq23393 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq23393
    | (have j0 := eq23393 X0
       grind)
    | exact resolve eq23393 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23393
  have eq23401 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq23397 X0
       have j1 := eq85 X0 X0
       grind)
    | (have r₁ := eq23397 x
       have r₂ := eq85 x x
       grind)
    | exact resolve eq23397 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23397
  have eq24512 : x ≠ (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq23401 x
       have i₂ := eq3183
       grind)
    | exact superpose eq3183 eq23401
    | (have j0 := eq23401 x
       grind)
    | exact resolve eq23401 eq3183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3183 eq23401
  have eq24542 : x ≠ y ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq24512
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq24512
    | exact resolve eq24512 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24512
  have eq28484 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq2418
       have i₂ := eq4916 x y
       grind)
    | exact superpose eq4916 eq2418
    | (have j1 := eq4916 x y
       grind)
    | (have r₁ := eq2418
       have r₂ := eq4916 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2418
       have r₂ := eq4916 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2418 eq4916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2418 eq4916
  have eq28493 : (σ (M.op x y)) = (σ x) ∨ y = (k x x) ∨ x = y := by grind
  clear eq28484
  have eq33354 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X1))) ≠ (σ (M.op X0 (M.op X0 X1))) ∨ (σ (M.op X0 (M.op X0 X1))) = (M.op (σ (M.op X0 (M.op X0 X1))) (σ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq647 (M.op X0 (M.op X0 X1))
       have i₂ := eq562 X0 X1 X0 X1
       grind)
    | exact superpose eq562 eq647
    | (have j0 := eq647 (M.op X0 (M.op X0 X1))
       grind)
    | exact resolve eq647 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq33403 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X1))) = (M.op (σ (M.op X0 (M.op X0 X1))) (σ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have j0 := eq33354 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33354
  have eq34475 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq4416
       grind)
    | exact superpose eq4416 eq9
    | exact resolve eq9 eq4416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4416
  have eq34584 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq34475
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq34475
    | exact resolve eq34475 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34475
  have eq35054 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq33 x x
       have i₂ := eq34584
       grind)
    | exact superpose eq34584 eq33
    | exact resolve eq33 eq34584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq34584
  have eq35073 : y = (M.op x x) ∨ x = y := by grind
  clear eq35054
  have eq35338 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X0 X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 x x
       have i₂ := eq35073
       grind)
    | exact superpose eq35073 eq18
    | exact resolve eq18 eq35073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35341 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op x y)) ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 x x X0 X1 X2
       have i₂ := eq35073
       grind)
    | exact superpose eq35073 eq57
    | exact resolve eq57 eq35073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq35073
  have eq35869 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq35338 X0 (M.op X0 x)
       have i₂ := eq35338 X0 x
       grind)
    | exact superpose eq35338 eq35338
    | exact resolve eq35338 eq35338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36146 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq35869 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35869
  have eq36946 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y := by grind
  have eq40863 : ∀ X0 X1 : G, (M.op x y) = (M.op X1 (M.op X0 (M.op x y))) ∨ x = y ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq35338 X1 (M.op X1 x)
       have i₂ := eq35341 X1 x X0
       grind)
    | (have i₁ := eq35338 x (M.op x y)
       have i₂ := eq35341 X0 X1 x
       grind)
    | exact superpose eq35341 eq35338
    | exact resolve eq35338 eq35341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35341
  have eq41022 : ∀ X0 X1 : G, (M.op x y) = (M.op X1 (M.op X0 (M.op x y))) ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq40863 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40863
  have eq43165 : x = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq36946
       have i₂ := eq3317
       grind)
    | exact superpose eq3317 eq36946
    | exact resolve eq36946 eq3317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3317 eq36946
  have eq43185 : x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq43165
       have r₂ := eq24542
       grind)
    | exact resolve eq43165 eq24542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24542 eq43165
  have eq43273 : x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq43185
       grind)
    | exact superpose eq43185 eq12
    | (have j0 := eq12 x x
       grind)
    | exact resolve eq12 eq43185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43185
  have eq43281 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq43273
  have eq43331 : x ≠ y ∨ x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq85 x x
       have i₂ := eq43281
       grind)
    | exact superpose eq43281 eq85
    | (have j0 := eq85 x x
       grind)
    | (have r₁ := eq85 x x
       have r₂ := eq43281
       grind)
    | exact resolve eq85 eq43281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43371 : x ≠ y ∨ x = (M.op x x) := by grind
  clear eq43281
  have eq43373 : x ≠ y ∨ x = (k x x) := by
    first
    | (have j1 := eq85 x x
       grind)
    | (have r₁ := eq43331
       have r₂ := eq85 x x
       grind)
    | exact resolve eq43331 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq43331
  have eq47264 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X1 X2 (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))
       have i₂ := eq3121 X0
       grind)
    | exact superpose eq3121 eq18
    | exact resolve eq18 eq3121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq47281 : ∀ X0 : G, (M.op x y) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq35338 (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))
       have i₂ := eq3121 X0
       grind)
    | exact superpose eq3121 eq35338
    | exact resolve eq35338 eq3121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47288 : ∀ X0 : G, (M.op x y) = (σ (M.op X0 (M.op X0 X0))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq47281 X0
       have i₂ := eq3121 X0
       grind)
    | exact superpose eq3121 eq47281
    | exact resolve eq47281 eq3121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3121 eq47281
  have eq47305 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47264 X0 X1 X2
       have i₂ := eq33403 X0 X0
       grind)
    | exact superpose eq33403 eq47264
    | exact resolve eq47264 eq33403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33403 eq47264
  have eq47598 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq47305 (M.op x y) X0 X1
       have i₂ := eq41022 (M.op x y) (M.op x y)
       grind)
    | exact superpose eq41022 eq47305
    | exact resolve eq47305 eq41022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47305
  have eq53635 : (M.op x y) = (σ (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq47288 (M.op x y)
       have i₂ := eq41022 (M.op x y) (M.op x y)
       grind)
    | exact superpose eq41022 eq47288
    | exact resolve eq47288 eq41022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41022 eq47288
  have eq53667 : (M.op x y) = (σ (M.op x y)) ∨ x = y := by grind
  clear eq53635
  have eq54011 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq6855 x x x
       have i₂ := eq47598 x (M.op x x)
       grind)
    | exact superpose eq47598 eq6855
    | (have r₁ := eq6855 x x x
       have r₂ := eq47598 x (M.op x x)
       grind)
    | exact resolve eq6855 eq47598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6855 eq47598
  have eq54101 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq54011
  have eq54151 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq54101
       grind)
    | exact superpose eq54101 eq14
    | exact resolve eq14 eq54101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54202 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq35338 (σ x) (σ y)
       have i₂ := eq54101
       grind)
    | exact superpose eq54101 eq35338
    | exact resolve eq35338 eq54101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35338
  have eq54229 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq54202
  have eq54263 : (M.op x y) ≠ (σ x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq54151
       have i₂ := eq53667
       grind)
    | exact superpose eq53667 eq54151
    | exact resolve eq54151 eq53667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53667
  have eq54264 : (σ x) ≠ (σ x) ∨ x = y ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq54151
       have i₂ := eq28493
       grind)
    | exact superpose eq28493 eq54151
    | (have r₁ := eq54151
       have r₂ := eq28493
       grind)
    | exact resolve eq54151 eq28493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28493 eq54151
  have eq54268 : (σ x) ≠ (σ x) ∨ x = y ∨ y = (k x x) := by grind
  clear eq54264
  have eq54269 : y = (k x x) ∨ x = y := by grind
  clear eq54268
  have eq54270 : (M.op x y) ≠ (σ x) ∨ x = y := by grind
  clear eq54263
  have eq56002 : (M.op x y) = (σ (k x x)) ∨ (M.op x y) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq35 x x
       have i₂ := eq54229
       grind)
    | exact superpose eq54229 eq35
    | exact resolve eq35 eq54229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq54229
  have eq56102 : (M.op x y) = (σ (k x x)) ∨ x = y := by
    first
    | (have r₁ := eq56002
       have r₂ := eq54270
       grind)
    | exact resolve eq56002 eq54270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56002
  have eq56149 : (M.op x y) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq56102
       have i₂ := eq54269
       grind)
    | exact superpose eq54269 eq56102
    | exact resolve eq56102 eq54269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54269 eq56102
  have eq56181 : (M.op x y) = (σ y) ∨ x = y := by grind
  clear eq56149
  have eq56198 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq36146 X0
       have i₂ := eq56181
       grind)
    | exact superpose eq56181 eq36146
    | exact resolve eq36146 eq56181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36146
  have eq56206 : (σ x) ≠ (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq54270
       have i₂ := eq56181
       grind)
    | exact superpose eq56181 eq54270
    | exact resolve eq54270 eq56181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54270 eq56181
  have eq56264 : (σ x) ≠ (σ y) ∨ x = y := by grind
  clear eq56206
  have eq56272 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq56198 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56198
  have eq57259 : (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq54101
       have i₂ := eq56272 (σ x)
       grind)
    | exact superpose eq56272 eq54101
    | exact resolve eq54101 eq56272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54101 eq56272
  have eq57266 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq57259
  have eq57279 : x = y := by
    first
    | (have r₁ := eq57266
       have r₂ := eq56264
       grind)
    | exact resolve eq57266 eq56264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56264 eq57266
  have eq57296 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq57279
       grind)
    | exact superpose eq57279 eq14
    | exact resolve eq14 eq57279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57310 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43371
       have i₂ := eq57279
       grind)
    | exact superpose eq57279 eq43371
    | (have r₁ := eq43371
       have r₂ := eq57279
       grind)
    | exact resolve eq43371 eq57279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43371
  have eq57311 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq43373
       have i₂ := eq57279
       grind)
    | exact superpose eq57279 eq43373
    | (have r₁ := eq43373
       have r₂ := eq57279
       grind)
    | exact resolve eq43373 eq57279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43373 eq57279
  have eq57314 : x = (k x x) := by grind
  clear eq57311
  have eq57315 : x = (M.op x x) := by grind
  clear eq57310
  have eq57322 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq57296
       have i₂ := eq57315
       grind)
    | exact superpose eq57315 eq57296
    | exact resolve eq57296 eq57315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57296 eq57315
  have eq57347 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq647 x
       have i₂ := eq57314
       grind)
    | exact superpose eq57314 eq647
    | (have j0 := eq647 x
       grind)
    | exact resolve eq647 eq57314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647 eq57314
  have eq57388 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq57347
  have eq57406 : False := by grind
  exact eq57406

/-- `Equation4279`: `x ◇ (x ◇ x) = y ◇ (z ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4279 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4279 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4279.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X2 X1)) := by
    intro X0 X1 X2
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
  have eq18 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X4 X3)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq8 x X3 X4
       have i₂ := eq8 x X0 X1
       grind)
    | (have i₁ := eq8 x X1 x
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X2 X3) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 (M.op X2 X3) X3
       have i₂ := eq8 X0 X3 X2
       grind)
    | (have i₁ := eq8 X0 (M.op X0 X0) X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq29 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25
    | exact resolve eq25 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq32 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op X3 X2)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 X3
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq38 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq43 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq57 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op X4 X5) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq18 X2 X3 (M.op X4 X5) X5
       have i₂ := eq18 X5 X4 X0 X1
       grind)
    | (have i₁ := eq18 X2 X3 (M.op X4 X5) X5
       have i₂ := eq18 X0 X1 X5 X4
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X2)) = (M.op (M.op X3 X4) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X2 (M.op X3 X4) X4
       have i₂ := eq18 X4 X3 X0 X1
       grind)
    | (have i₁ := eq8 X2 (M.op X3 X4) X4
       have i₂ := eq18 X0 X1 X4 X3
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq28
    | exact resolve eq28 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq33
    | exact resolve eq33 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq33 (τ X1) X0
       grind)
    | exact superpose eq33 eq17
    | (have j1 := eq33 (τ X1) X0
       grind)
    | exact resolve eq17 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq33 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq29 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq29
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq29 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq146 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq43
  have eq160 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq146 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq146
    | exact resolve eq146 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq212 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (k (M.op X1 (M.op X1 X1)) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    grind
  clear eq21
  have eq286 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14
       have i₂ := eq32 (σ y) (σ x) X0 X1
       grind)
    | exact superpose eq32 eq14
    | (have j1 := eq32 (σ y) (σ x) x x
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq312 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq286 X0 X1
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq286
    | (have j0 := eq286 X0 X1
       grind)
    | exact resolve eq286 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq419 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq160 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq160 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq160
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq160 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq535 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq35 x y
       grind)
    | exact superpose eq35 eq14
    | (have j1 := eq35 x y
       grind)
    | exact resolve eq14 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq9
    | (have j1 := eq35 X0 X1
       grind)
    | exact resolve eq9 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq584 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq35 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1370 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq584 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq584
    | (have j0 := eq584 (τ X0)
       grind)
    | exact resolve eq584 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq1372 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1370 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1370
    | (have j0 := eq1370 X0
       grind)
    | exact resolve eq1370 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370
  have eq1375 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1372 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1372
    | (have j0 := eq1372 X0
       grind)
    | exact resolve eq1372 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1372
  have eq1398 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq38
    | exact resolve eq38 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1461 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq10
    | (have j1 := eq38 X0 X1
       grind)
    | exact resolve eq10 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1489 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1398 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1398
    | (have j0 := eq1398 X0 X1
       grind)
    | exact resolve eq1398 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398
  have eq1511 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1375 (τ X0)
       have i₂ := eq70 X0 X0
       grind)
    | exact superpose eq70 eq1375
    | (have j0 := eq1375 (τ X0)
       grind)
    | exact resolve eq1375 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq1375
  have eq1513 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq82
    | exact resolve eq82 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq1554 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1513 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1513
    | (have j0 := eq1513 X0 X1
       grind)
    | exact resolve eq1513 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513
  have eq2039 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X2 X3 (σ X1) (σ X0)
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq18
    | (have j1 := eq79 X0 X1
       grind)
    | exact resolve eq18 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq2408 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq535
       have i₂ := eq1554 y x
       grind)
    | exact superpose eq1554 eq535
    | (have j1 := eq1554 y x
       grind)
    | (have r₁ := eq535
       have r₂ := eq1554 y x
       grind)
    | exact resolve eq535 eq1554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554
  have eq2409 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq535
       have i₂ := eq1489 y x
       grind)
    | exact superpose eq1489 eq535
    | (have j1 := eq1489 (σ y) (σ x)
       grind)
    | (have r₁ := eq535
       have r₂ := eq1489 y x
       grind)
    | exact resolve eq535 eq1489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535
  have eq2410 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2409
  have eq2411 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq2408
  have eq2423 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq160 x
       have i₂ := eq2410
       grind)
    | exact superpose eq2410 eq160
    | exact resolve eq160 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2456 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2423
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2423
    | exact resolve eq2423 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2423
  have eq2536 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq2456
       grind)
    | exact superpose eq2456 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq2456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2539 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1489 y x
       have i₂ := eq2456
       grind)
    | exact superpose eq2456 eq1489
    | (have j0 := eq1489 y x
       grind)
    | exact resolve eq1489 eq2456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489 eq2456
  have eq2540 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq2539
  have eq2541 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq2536
  have eq2591 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq554 x x
       have i₂ := eq2410
       grind)
    | exact superpose eq2410 eq554
    | exact resolve eq554 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq2633 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2591
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2591
    | exact resolve eq2591 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2591
  have eq2646 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 y x
       have i₂ := eq2541
       grind)
    | exact superpose eq2541 eq18
    | exact resolve eq18 eq2541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3776 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq160 x
       have i₂ := eq2411
       grind)
    | exact superpose eq2411 eq160
    | exact resolve eq160 eq2411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq2411
  have eq3824 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq3776
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3776
    | exact resolve eq3776 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3776
  have eq3825 : x = (k x y) := by grind
  clear eq3824
  have eq5341 : (M.op (σ x) (σ y)) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2646 (σ x) (σ x)
       have i₂ := eq2410
       grind)
    | exact superpose eq2410 eq2646
    | exact resolve eq2646 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5461 : (M.op (σ x) (σ y)) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq5341
  have eq5885 : (σ (M.op x y)) ≠ (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq5461
       grind)
    | exact superpose eq5461 eq14
    | exact resolve eq14 eq5461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5461
  have eq6348 : (σ x) ≠ (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5885
       have i₂ := eq2540
       grind)
    | exact superpose eq2540 eq5885
    | exact resolve eq5885 eq2540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2540 eq5885
  have eq6349 : (σ x) ≠ (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq6348
  have eq8009 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
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
  have eq8086 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8009 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq8009
    | (have j0 := eq8009 X0 X1
       grind)
    | exact resolve eq8009 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8009
  have eq21291 : ∀ X0 : G, (τ (σ X0)) ≠ (τ (M.op (σ X0) (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1511 (σ X0)
       have i₂ := eq419 (σ X0) X0
       grind)
    | exact superpose eq419 eq1511
    | (have j0 := eq1511 (σ X0)
       have j1 := eq419 (σ X0) X0
       grind)
    | exact resolve eq1511 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq21315 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq21291 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq21291
    | (have j0 := eq21291 X0
       grind)
    | exact resolve eq21291 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21291
  have eq21323 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq21315 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq21315
    | (have j0 := eq21315 X0
       grind)
    | exact resolve eq21315 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21315
  have eq21325 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq21323 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq21323
    | (have j0 := eq21323 X0
       grind)
    | exact resolve eq21323 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21323
  have eq21327 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq21325 X0
       have j1 := eq85 X0 X0
       grind)
    | (have r₁ := eq21325 x
       have r₂ := eq85 x x
       grind)
    | exact resolve eq21325 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq21325
  have eq22214 : x ≠ (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq21327 x
       have i₂ := eq2410
       grind)
    | exact superpose eq2410 eq21327
    | (have j0 := eq21327 x
       grind)
    | exact resolve eq21327 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21327
  have eq22240 : x ≠ y ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq22214
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq22214
    | exact resolve eq22214 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22214
  have eq25535 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq2633
       grind)
    | exact superpose eq2633 eq9
    | exact resolve eq9 eq2633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2633
  have eq25604 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq25535
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq25535
    | exact resolve eq25535 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25535
  have eq26593 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq33 x x
       have i₂ := eq25604
       grind)
    | exact superpose eq25604 eq33
    | exact resolve eq33 eq25604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq25604
  have eq26606 : y = (M.op x x) ∨ x = y := by grind
  clear eq26593
  have eq27635 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 X0)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 x x
       have i₂ := eq26606
       grind)
    | exact superpose eq26606 eq18
    | exact resolve eq18 eq26606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26606
  have eq28743 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) (M.op x y)) ∨ x = y ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq27635 (M.op X0 X1) X1
       have i₂ := eq27635 X1 X0
       grind)
    | exact superpose eq27635 eq27635
    | exact resolve eq27635 eq27635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27635
  have eq29070 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) (M.op x y)) ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq28743 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28743
  have eq32461 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y := by grind
  clear eq29070
  have eq33274 : x = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq32461
       have i₂ := eq2541
       grind)
    | exact superpose eq2541 eq32461
    | exact resolve eq32461 eq2541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2541 eq32461
  have eq33332 : x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq33274
       have r₂ := eq22240
       grind)
    | exact resolve eq33274 eq22240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22240 eq33274
  have eq34362 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq584 x
       have i₂ := eq33332
       grind)
    | exact superpose eq33332 eq584
    | (have j0 := eq584 x
       grind)
    | exact resolve eq584 eq33332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq33332
  have eq34386 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq34362
  have eq41020 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2410
       have i₂ := eq34386
       grind)
    | exact superpose eq34386 eq2410
    | exact resolve eq2410 eq34386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2410
  have eq41169 : (M.op (σ x) (σ x)) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2646 (σ x) (σ x)
       have i₂ := eq34386
       grind)
    | exact superpose eq34386 eq2646
    | exact resolve eq2646 eq34386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2646
  have eq41173 : (M.op (σ x) (σ x)) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq41169
  have eq41178 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq41020
  have eq50975 : (σ x) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq34386
       have i₂ := eq41173
       grind)
    | exact superpose eq41173 eq34386
    | exact resolve eq34386 eq41173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34386 eq41173
  have eq51084 : (σ x) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq50975
  have eq51093 : y = (M.op x x) := by
    first
    | (have r₁ := eq51084
       have r₂ := eq6349
       grind)
    | exact resolve eq51084 eq6349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6349 eq51084
  have eq52251 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq212 X0 x
       have i₂ := eq51093
       grind)
    | exact superpose eq51093 eq212
    | exact resolve eq212 eq51093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq52278 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 x x
       have i₂ := eq51093
       grind)
    | exact superpose eq51093 eq18
    | exact resolve eq18 eq51093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq52282 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X3) (M.op x y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 x x X0 X1 X2 X3
       have i₂ := eq51093
       grind)
    | exact superpose eq51093 eq57
    | exact resolve eq57 eq51093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq52286 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op X1 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 X1 X2 X0 x x
       have i₂ := eq51093
       grind)
    | exact superpose eq51093 eq69
    | exact resolve eq69 eq51093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq51093
  have eq52362 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq52251 x
       have i₂ := eq52278 x x
       grind)
    | exact superpose eq52278 eq52251
    | exact resolve eq52251 eq52278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52251
  have eq53771 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq52278 (M.op X0 X1) X1
       have i₂ := eq52278 X1 X0
       grind)
    | exact superpose eq52278 eq52278
    | exact resolve eq52278 eq52278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57047 : (τ (M.op x y)) ≠ (τ (M.op x y)) ∨ (τ (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) := by
    first
    | (have i₁ := eq1511 (M.op x y)
       have i₂ := eq52362
       grind)
    | exact superpose eq52362 eq1511
    | (have j0 := eq1511 (M.op x y)
       grind)
    | exact resolve eq1511 eq52362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511 eq52362
  have eq57061 : (τ (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) := by grind
  clear eq57047
  have eq63093 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq1461 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1461
  have eq63094 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq63093 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq63093
    | (have j0 := eq63093 X0
       grind)
    | exact resolve eq63093 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63093
  have eq63140 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq63094 (σ X0)
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq63094
    | (have j0 := eq63094 (σ X0)
       grind)
    | exact resolve eq63094 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63094
  have eq63150 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq63140 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq63140
    | (have j0 := eq63140 X0
       grind)
    | exact resolve eq63140 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63140
  have eq71931 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq63150 X0
       have i₂ := eq8086 X0 X0
       grind)
    | exact superpose eq8086 eq63150
    | (have j0 := eq63150 X0
       have j1 := eq8086 X0 X0
       grind)
    | (have r₁ := eq63150 x
       have r₂ := eq8086 x x
       grind)
    | exact resolve eq63150 eq8086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8086 eq63150
  have eq71938 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq71931 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71931
  have eq71968 : (σ x) = (σ y) ∨ y = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq71938 x
       have i₂ := eq41178
       grind)
    | exact superpose eq41178 eq71938
    | exact resolve eq71938 eq41178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41178 eq71938
  have eq72004 : y = (k x x) ∨ (σ x) = (σ y) := by grind
  clear eq71968
  have eq74048 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq52282 (τ (M.op x y)) (τ (M.op x y)) X0 X1
       have i₂ := eq57061
       grind)
    | exact superpose eq57061 eq52282
    | exact resolve eq52282 eq57061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52282
  have eq74054 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (τ (M.op x y)) (τ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq52286 X0 (τ (M.op x y)) (τ (M.op x y))
       have i₂ := eq57061
       grind)
    | exact superpose eq57061 eq52286
    | exact resolve eq52286 eq57061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52286
  have eq74056 : (M.op x y) = (M.op (τ (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq53771 (τ (M.op x y)) (τ (M.op x y))
       have i₂ := eq57061
       grind)
    | exact superpose eq57061 eq53771
    | exact resolve eq53771 eq57061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74059 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (τ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq74054 X0
       have i₂ := eq57061
       grind)
    | exact superpose eq57061 eq74054
    | exact resolve eq74054 eq57061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74054
  have eq74065 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op x y)) = (τ (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq74048 X0 X1
       have i₂ := eq57061
       grind)
    | exact superpose eq57061 eq74048
    | exact resolve eq74048 eq57061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57061 eq74048
  have eq74173 : (M.op x y) = (M.op y (τ (M.op x y))) := by
    first
    | (have i₁ := eq74059 x
       have i₂ := eq52278 x x
       grind)
    | exact superpose eq52278 eq74059
    | exact resolve eq74059 eq52278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74059
  have eq74177 : (M.op x y) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq74065 x x
       have i₂ := eq53771 x x
       grind)
    | exact superpose eq53771 eq74065
    | exact resolve eq74065 eq53771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53771 eq74065
  have eq74351 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq74177
       grind)
    | exact superpose eq74177 eq10
    | exact resolve eq10 eq74177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74177
  have eq74568 : (σ (M.op x y)) ≠ (M.op (τ (M.op x y)) (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq312 (τ (M.op x y)) y
       have i₂ := eq74173
       grind)
    | exact superpose eq74173 eq312
    | exact resolve eq312 eq74173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312 eq74173
  have eq74622 : (M.op x y) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq74568
       have i₂ := eq74056
       grind)
    | exact superpose eq74056 eq74568
    | exact resolve eq74568 eq74056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74056 eq74568
  have eq74668 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have r₁ := eq74622
       have r₂ := eq74351
       grind)
    | exact resolve eq74622 eq74351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74622
  have eq74681 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74668
       have i₂ := eq3825
       grind)
    | exact superpose eq3825 eq74668
    | exact resolve eq74668 eq3825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3825 eq74668
  have eq74727 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq74681
       grind)
    | exact superpose eq74681 eq14
    | exact resolve eq14 eq74681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74843 : (M.op x y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq52278 (σ y) (σ x)
       have i₂ := eq74681
       grind)
    | exact superpose eq74681 eq52278
    | exact resolve eq52278 eq74681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74960 : (M.op x y) ≠ (σ x) := by
    first
    | (have i₁ := eq74727
       have i₂ := eq74351
       grind)
    | exact superpose eq74351 eq74727
    | exact resolve eq74727 eq74351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74351 eq74727
  have eq76765 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X1 X0)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq2039 x x x x
       have i₂ := eq72004
       grind)
    | exact superpose eq72004 eq2039
    | exact resolve eq2039 eq72004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2039 eq72004
  have eq76809 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X1 X0)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have j0 := eq76765 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76765
  have eq76821 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq76809 x x
       have i₂ := eq52278 x x
       grind)
    | exact superpose eq52278 eq76809
    | exact resolve eq76809 eq52278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52278 eq76809
  have eq76839 : (M.op x y) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq76821
       have i₂ := eq74681
       grind)
    | exact superpose eq74681 eq76821
    | exact resolve eq76821 eq74681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76821
  have eq76841 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq76839
       have r₂ := eq74960
       grind)
    | exact resolve eq76839 eq74960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76839
  have eq76843 : (M.op x y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq74843
       have i₂ := eq76841
       grind)
    | exact superpose eq76841 eq74843
    | exact resolve eq74843 eq76841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74843
  have eq76844 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq74681
       have i₂ := eq76841
       grind)
    | exact superpose eq76841 eq74681
    | exact resolve eq74681 eq76841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74681 eq76841
  have eq76946 : (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq76843
       have i₂ := eq76844
       grind)
    | exact superpose eq76844 eq76843
    | exact resolve eq76843 eq76844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76843 eq76844
  have eq76948 : False := by grind
  exact eq76948

/-- `Equation4297`: `x ◇ (x ◇ y) = y ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pyy_pxy_Equation4297 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law4297 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4297.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op X2 X2)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) (M.op X3 X3)) = (M.op X2 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X2 X0) X3
       have i₂ := eq8 X2 X0 X1
       grind)
    | (have i₁ := eq8 X1 (M.op X2 X2) X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op X1 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 (M.op X2 X2) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | (have i₁ := eq8 X0 (M.op X0 X1) X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 x X0 X3
       have i₂ := eq8 x X0 X1
       grind)
    | (have i₁ := eq8 x x x
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X2 X1 x
       grind)
    | (have i₁ := eq8 X0 X1 X1
       have i₂ := eq8 X1 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq46 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq60 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (M.op X1 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    grind
  have eq63 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X2 (k X0 (M.op X0 X0))) := by
    intro X0 X1 X2
    grind
  have eq65 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 (k (τ X0) X1) X2
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq34
    | exact resolve eq34 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op X3 (M.op (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X0 X0)
       have i₂ := eq24 (M.op X0 X0) X0 X1
       grind)
    | (have i₁ := eq8 X2 X3 (M.op X0 X0)
       have i₂ := eq24 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq24 eq8
    | exact resolve eq8 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = (M.op X2 (M.op X2 (M.op X3 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq28 X2 (M.op X3 X3) X1
       have i₂ := eq8 X0 X1 X3
       grind)
    | (have i₁ := eq28 X0 (M.op X0 X1) X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq28
    | exact resolve eq28 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq174 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = (k X2 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 X2 X1
       have i₂ := eq8 X0 X1 X2
       grind)
    | (have i₁ := eq60 X1 X1
       have i₂ := eq8 X1 X1 X2
       grind)
    | exact superpose eq8 eq60
    | exact resolve eq60 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (k X1 (σ (M.op (τ X1) (τ X1)))) = (σ (M.op X0 (M.op X0 (M.op (τ X1) (τ X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op (τ X1) (τ X1))
       have i₂ := eq60 (τ X1) X0
       grind)
    | exact superpose eq60 eq16
    | exact resolve eq16 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq228 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 (k X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 X0
       have i₂ := eq63 X1 X0 X0
       grind)
    | exact superpose eq63 eq60
    | exact resolve eq60 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq63
  have eq358 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq462 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op X1 (M.op X2 X2))) = (M.op X0 (M.op X1 (M.op X4 X4))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq22 X1 X4 X0 x
       have i₂ := eq22 X1 X2 X0 x
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq721 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op X3 (M.op X0 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op x x)
       have i₂ := eq23 X1 X0 x x
       grind)
    | exact superpose eq23 eq8
    | exact resolve eq8 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq1705 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq358 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq1781 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq1705 (σ X0)
       grind)
    | exact superpose eq1705 eq13
    | exact resolve eq13 eq1705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1783 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46 X0 X0
       have i₂ := eq1705 (τ X0)
       grind)
    | exact superpose eq1705 eq46
    | exact resolve eq46 eq1705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1790 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1783 X0
       have i₂ := eq1705 X0
       grind)
    | exact superpose eq1705 eq1783
    | exact resolve eq1783 eq1705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1783
  have eq1792 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1781 X0
       have i₂ := eq1705 X0
       grind)
    | exact superpose eq1705 eq1781
    | exact resolve eq1781 eq1705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1705 eq1781
  have eq1957 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 X1))) = (k (τ X0) (τ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq174 X2 X1 (τ X0)
       have i₂ := eq1790 X0
       grind)
    | exact superpose eq1790 eq174
    | exact resolve eq174 eq1790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1790
  have eq1982 : ∀ X0 X1 X2 : G, (τ (k X0 (M.op X0 X0))) = (M.op X1 (M.op X2 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1957 X0 X1 X2
       have i₂ := eq46 (M.op X0 X0) X0
       grind)
    | exact superpose eq46 eq1957
    | exact resolve eq1957 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957
  have eq2061 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq9
    | (have j1 := eq43 X0 X1
       grind)
    | exact resolve eq9 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq2133 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2061 X0 X1
       have i₂ := eq1792 X0
       grind)
    | exact superpose eq1792 eq2061
    | (have j0 := eq2061 X0 X1
       grind)
    | exact resolve eq2061 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2061
  have eq2202 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2133 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq2133
    | (have j0 := eq2133 X0 X1
       grind)
    | exact resolve eq2133 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2133
  have eq2269 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X2 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 (σ X0)
       have i₂ := eq1792 X0
       grind)
    | exact superpose eq1792 eq8
    | exact resolve eq8 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2277 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 X2 (σ X0)
       have i₂ := eq1792 X0
       grind)
    | exact superpose eq1792 eq24
    | exact resolve eq24 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3962 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (σ (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2277 (σ X0) X1 X2
       have i₂ := eq1792 X0
       grind)
    | exact superpose eq1792 eq2277
    | exact resolve eq2277 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1792
  have eq14827 : ∀ X0 X1 : G, (M.op (k X1 (M.op X1 X1)) X0) = (k (k X1 (M.op X1 X1)) X0) ∨ (M.op (k X1 (M.op X1 X1)) X0) = (k (k X1 (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq228 (k X1 (M.op X1 X1)) X1
       have i₂ := eq12 (k X1 (M.op X1 X1)) X1
       grind)
    | (have i₁ := eq228 X0 X1
       have i₂ := eq12 X0 (M.op X0 (k X1 (M.op X1 X1)))
       grind)
    | exact superpose eq12 eq228
    | (have j1 := eq12 (k X1 (M.op X1 X1)) X0
       grind)
    | exact resolve eq228 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq14931 : ∀ X0 X1 : G, (M.op (k X1 (M.op X1 X1)) X0) = (k (k X1 (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq14827 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14827
  have eq26928 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2202 x y
       grind)
    | exact superpose eq2202 eq14
    | (have j1 := eq2202 x y
       grind)
    | exact resolve eq14 eq2202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2202
  have eq27429 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq26928
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq26928
    | (have j1 := eq12 x y
       grind)
    | exact resolve eq26928 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26928
  have eq27435 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq27429
  have eq27436 : y = (M.op x x) := by grind
  clear eq27435
  have eq27673 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq8
    | exact resolve eq8 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27679 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1 x
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq24
    | exact resolve eq24 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq27699 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op (M.op X2 X2) y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq111 X2 x X0 X1
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq111
    | exact resolve eq111 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq27722 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 X2))) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq462 X0 X1 X2 x
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq462
    | exact resolve eq462 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq27752 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq2269 x X0 X1
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq2269
    | exact resolve eq2269 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269
  have eq27753 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq2277 x X0 X1
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq2277
    | exact resolve eq2277 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2277
  have eq27779 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq144 x x X0 X1
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq144
    | exact resolve eq144 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq27781 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq174 x x X0
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq174
    | exact resolve eq174 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq27786 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op x (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq721 x x X0 X1
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq721
    | exact resolve eq721 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq27788 : ∀ X0 : G, (τ (k X0 (M.op X0 X0))) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1982 X0 x x
       have i₂ := eq27436
       grind)
    | exact superpose eq27436 eq1982
    | exact resolve eq1982 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1982 eq27436
  have eq27833 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X0 (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq27722 X0 X1 x
       have i₂ := eq27753 X1 x
       grind)
    | exact superpose eq27753 eq27722
    | exact resolve eq27722 eq27753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27722
  have eq27850 : ∀ X1 X2 : G, (M.op X1 (M.op (M.op X2 X2) y)) = (M.op X1 (σ y)) := by
    intro X1 X2
    first
    | (have i₁ := eq27699 x X1 X2
       have i₂ := eq27752 x X1
       grind)
    | exact superpose eq27752 eq27699
    | exact resolve eq27699 eq27752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27699
  have eq35877 : ∀ X0 X1 : G, (M.op X0 (σ (σ (M.op X1 X1)))) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq3962 X1 X0 X0
       have i₂ := eq27673 X0 X0
       grind)
    | exact superpose eq27673 eq3962
    | exact resolve eq3962 eq27673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52167 : ∀ X0 X1 X2 : G, (M.op X1 (σ (σ (M.op X2 X2)))) = (M.op X1 (M.op (M.op X0 X0) y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3962 X2 X1 (M.op X0 X0)
       have i₂ := eq27679 (M.op X0 X0) X0
       grind)
    | exact superpose eq27679 eq3962
    | exact resolve eq3962 eq27679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3962 eq27679
  have eq52290 : ∀ X1 X2 : G, (M.op X1 (σ (σ (M.op X2 X2)))) = (M.op X1 (σ y)) := by
    intro X1 X2
    first
    | (have i₁ := eq52167 x X1 X2
       have i₂ := eq27850 X1 x
       grind)
    | exact superpose eq27850 eq52167
    | exact resolve eq52167 eq27850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27850 eq52167
  have eq52670 : ∀ X1 : G, (M.op X1 y) = (M.op X1 (σ y)) := by
    intro X1
    first
    | (have i₁ := eq52290 X1 x
       have i₂ := eq35877 X1 x
       grind)
    | exact superpose eq35877 eq52290
    | exact resolve eq52290 eq35877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35877 eq52290
  have eq56146 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq52670 (σ x)
       grind)
    | exact superpose eq52670 eq14
    | exact resolve eq14 eq52670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134979 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X1 (M.op (τ X0) (τ X0)))) (τ X2)) = (τ (k (k X0 (σ (M.op (τ X0) (τ X0)))) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 (M.op X1 (M.op X1 (M.op (τ X0) (τ X0)))) X2
       have i₂ := eq185 X1 X0
       grind)
    | exact superpose eq185 eq34
    | exact resolve eq34 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq185
  have eq134998 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X1 (M.op (τ X0) (τ X0)))) (τ X2)) = (k (k (τ X0) (M.op (τ X0) (τ X0))) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq134979 X0 X1 X2
       have i₂ := eq65 X0 (M.op (τ X0) (τ X0)) X2
       grind)
    | exact superpose eq65 eq134979
    | exact resolve eq134979 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq134979
  have eq135201 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X1 (M.op (τ X0) (τ X0)))) (τ X2)) = (M.op (k (τ X0) (M.op (τ X0) (τ X0))) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq134998 X0 X1 X2
       have i₂ := eq14931 (τ X2) (τ X0)
       grind)
    | exact superpose eq14931 eq134998
    | exact resolve eq134998 eq14931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134998
  have eq135395 : ∀ X0 X1 X2 : G, (M.op (M.op x (M.op x y)) (τ X2)) = (k (M.op X1 (M.op X1 (M.op (τ X0) (τ X0)))) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq135201 X0 X1 X2
       have i₂ := eq27781 (τ X0)
       grind)
    | exact superpose eq27781 eq135201
    | exact resolve eq135201 eq27781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135201
  have eq135579 : ∀ X2 : G, (M.op (M.op x (M.op x y)) (τ X2)) = (k (M.op x (M.op x y)) (τ X2)) := by
    intro X2
    first
    | (have i₁ := eq135395 x x X2
       have i₂ := eq27779 x (τ x)
       grind)
    | exact superpose eq27779 eq135395
    | exact resolve eq135395 eq27779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27779 eq135395
  have eq135740 : ∀ X2 : G, (M.op (M.op y (σ y)) (τ X2)) = (k (M.op y (σ y)) (τ X2)) := by
    intro X2
    first
    | (have i₁ := eq135579 X2
       have i₂ := eq27752 x y
       grind)
    | exact superpose eq27752 eq135579
    | exact resolve eq135579 eq27752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135579
  have eq135891 : ∀ X2 : G, (M.op (M.op y y) (τ X2)) = (k (M.op y y) (τ X2)) := by
    intro X2
    first
    | (have i₁ := eq135740 X2
       have i₂ := eq52670 y
       grind)
    | exact superpose eq52670 eq135740
    | exact resolve eq135740 eq52670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135740
  have eq340913 : ∀ X0 X1 : G, (τ (k (k X0 (M.op X0 X0)) X1)) = (k (M.op x (M.op x y)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X1 (k X0 (M.op X0 X0))
       have i₂ := eq27788 X0
       grind)
    | exact superpose eq27788 eq46
    | exact resolve eq46 eq27788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq27788
  have eq340915 : ∀ X0 X1 : G, (τ (k (k X0 (M.op X0 X0)) X1)) = (k (M.op y (σ y)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq340913 X0 X1
       have i₂ := eq27752 x y
       grind)
    | exact superpose eq27752 eq340913
    | exact resolve eq340913 eq27752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340913
  have eq340990 : ∀ X0 X1 : G, (k (M.op y y) (τ X1)) = (τ (k (k X0 (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq340915 X0 X1
       have i₂ := eq52670 y
       grind)
    | exact superpose eq52670 eq340915
    | exact resolve eq340915 eq52670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340915
  have eq341065 : ∀ X0 X1 : G, (k (M.op y y) (τ X1)) = (τ (M.op (k X0 (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq340990 X0 X1
       have i₂ := eq14931 X1 X0
       grind)
    | exact superpose eq14931 eq340990
    | exact resolve eq340990 eq14931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14931 eq340990
  have eq341136 : ∀ X1 : G, (k (M.op y y) (τ X1)) = (τ (M.op (M.op x (M.op x y)) X1)) := by
    intro X1
    first
    | (have i₁ := eq341065 x X1
       have i₂ := eq27781 x
       grind)
    | exact superpose eq27781 eq341065
    | exact resolve eq341065 eq27781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27781 eq341065
  have eq341187 : ∀ X1 : G, (k (M.op y y) (τ X1)) = (τ (M.op (M.op y (σ y)) X1)) := by
    intro X1
    first
    | (have i₁ := eq341136 X1
       have i₂ := eq27752 x y
       grind)
    | exact superpose eq27752 eq341136
    | exact resolve eq341136 eq27752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341136
  have eq341228 : ∀ X1 : G, (k (M.op y y) (τ X1)) = (τ (M.op (M.op y y) X1)) := by
    intro X1
    first
    | (have i₁ := eq341187 X1
       have i₂ := eq52670 y
       grind)
    | exact superpose eq52670 eq341187
    | exact resolve eq341187 eq52670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341187
  have eq341257 : ∀ X1 : G, (M.op (M.op y y) (τ X1)) = (τ (M.op (M.op y y) X1)) := by
    intro X1
    first
    | (have i₁ := eq341228 X1
       have i₂ := eq135891 X1
       grind)
    | exact superpose eq135891 eq341228
    | exact resolve eq341228 eq135891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135891 eq341228
  have eq563820 : ∀ X0 : G, (τ (M.op X0 y)) = (M.op (M.op y y) (τ (M.op (M.op y y) X0))) := by
    intro X0
    first
    | (have i₁ := eq341257 (M.op (M.op y y) X0)
       have i₂ := eq27673 (M.op y y) X0
       grind)
    | exact superpose eq27673 eq341257
    | exact resolve eq341257 eq27673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27673
  have eq563944 : ∀ X0 : G, (τ (M.op X0 y)) = (M.op (M.op y y) (M.op (M.op y y) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq563820 X0
       have i₂ := eq341257 X0
       grind)
    | exact superpose eq341257 eq563820
    | exact resolve eq563820 eq341257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341257 eq563820
  have eq564013 : ∀ X0 : G, (M.op (τ X0) (M.op x (M.op x y))) = (τ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq563944 X0
       have i₂ := eq27786 (M.op y y) (τ X0)
       grind)
    | exact superpose eq27786 eq563944
    | exact resolve eq563944 eq27786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27786 eq563944
  have eq564072 : ∀ X0 : G, (M.op (τ X0) (M.op y (σ y))) = (τ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq564013 X0
       have i₂ := eq27752 x y
       grind)
    | exact superpose eq27752 eq564013
    | exact resolve eq564013 eq27752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27752 eq564013
  have eq564123 : ∀ X0 : G, (M.op (τ X0) (M.op y y)) = (τ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq564072 X0
       have i₂ := eq27833 (τ X0) y
       grind)
    | exact superpose eq27833 eq564072
    | exact resolve eq564072 eq27833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27833 eq564072
  have eq564165 : ∀ X0 : G, (M.op (τ X0) (σ y)) = (τ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq564123 X0
       have i₂ := eq27753 (τ X0) y
       grind)
    | exact superpose eq27753 eq564123
    | exact resolve eq564123 eq27753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27753 eq564123
  have eq564186 : ∀ X0 : G, (M.op (τ X0) y) = (τ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq564165 X0
       have i₂ := eq52670 (τ X0)
       grind)
    | exact superpose eq52670 eq564165
    | exact resolve eq564165 eq52670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52670 eq564165
  have eq567288 : ∀ X0 : G, (M.op X0 y) = (σ (M.op (τ X0) y)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 y)
       have i₂ := eq564186 X0
       grind)
    | exact superpose eq564186 eq10
    | exact resolve eq10 eq564186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564186
  have eq569280 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq567288 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq567288
    | exact resolve eq567288 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567288
  have eq570319 : (M.op (σ x) y) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq56146
       have i₂ := eq569280 x
       grind)
    | exact superpose eq569280 eq56146
    | (have r₁ := eq56146
       have r₂ := eq569280 x
       grind)
    | exact resolve eq56146 eq569280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56146 eq569280
  have eq570329 : False := by grind
  exact eq570329
