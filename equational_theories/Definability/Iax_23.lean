import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4441`: `x ◇ (y ◇ x) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_y_x_pyx_Equation4441 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4441 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4441.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X3) := by
    intro X0 X1 X2 X3
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq18 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X2 X4) X5) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq8 X2 (M.op X0 x) X4 X5
       have i₂ := eq8 X0 X1 x X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X5) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq8 X0 x X4 X5
       have i₂ := eq8 X0 x X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x x
       have i₂ := eq8 X0 X2 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 X0)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X0 X4 X1 (M.op x (M.op X0 X1))
       have i₂ := eq8 (M.op X0 X1) x X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq32 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq66 : ∀ X0 X1 X2 X3 X5 X6 : G, (M.op (M.op X3 X5) X6) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X5 X6
    first
    | (have i₁ := eq8 X3 (M.op X0 x) X5 X6
       have i₂ := eq19 X0 x X3 X1 X2
       grind)
    | (have i₁ := eq8 X3 (M.op X0 x) X5 X6
       have i₂ := eq19 X0 X1 X2 x X3
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30
    | exact resolve eq30 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq95 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X1 X0))) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X2 X3 (M.op X0 x)
       have i₂ := eq8 X0 X1 x X2
       grind)
    | exact superpose eq8 eq23
    | exact resolve eq23 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X3 X4) X5) = (M.op X3 (M.op X6 (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq18 X6 (M.op X0 x) X3 X4 X5
       have i₂ := eq19 X0 x X6 X1 X2
       grind)
    | (have i₁ := eq18 X6 (M.op X0 x) X3 X4 X5
       have i₂ := eq19 X0 X1 X2 x X6
       grind)
    | exact superpose eq19 eq18
    | exact resolve eq18 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq285 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op (M.op X0 X2) X3) ∨ (k X4 (M.op (M.op X0 X2) X3)) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq11 X4 (M.op (M.op X0 X2) X3)
       have i₂ := eq24 X0 X2 X3 X4 X1
       grind)
    | exact superpose eq24 eq11
    | (have j0 := eq11 X4 (M.op (M.op X0 X2) X3)
       grind)
    | exact resolve eq11 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq297 : ∀ X0 X2 X3 X4 : G, (k X4 (M.op (M.op X0 X2) X3)) = X4 := by
    intro X0 X2 X3 X4
    first
    | (have j0 := eq285 X0 x X2 X3 X4
       grind)
    | (have r₁ := eq285 X0 x X2 X3 X4
       have r₂ := eq8 X0 x X2 X3
       grind)
    | exact resolve eq285 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq817 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
  have eq841 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq1698 : ∀ X0 X1 X2 X3 X4 X6 : G, (M.op X3 (M.op X6 X3)) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X1))))) := by
    intro X0 X1 X2 X3 X4 X6
    first
    | (have i₁ := eq95 X4 (M.op X0 x) X3 X6
       have i₂ := eq18 X1 X2 X0 x X4
       grind)
    | exact superpose eq18 eq95
    | exact resolve eq95 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1764 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X4 (M.op X0 (M.op (M.op X1 X2) X3))) = (M.op X4 (M.op X5 (M.op X6 X5))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq95 X5 X6 X4 (M.op X0 x)
       have i₂ := eq66 X1 X2 X3 X0 x X4
       grind)
    | exact superpose eq66 eq95
    | exact resolve eq95 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq3567 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 X8 : G, (M.op (M.op X5 X6) X7) = (M.op X5 (M.op X8 (M.op X0 (M.op X1 (M.op (M.op X2 X3) X4))))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7 X8
    first
    | (have i₁ := eq18 X8 (M.op X0 x) X5 X6 X7
       have i₂ := eq155 X2 X3 X4 X0 x X8 X1
       grind)
    | exact superpose eq155 eq18
    | exact resolve eq18 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq7521 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq841 (τ X1) (τ X0)
       have i₂ := eq69 X1 X0
       grind)
    | exact superpose eq69 eq841
    | (have j0 := eq841 (τ X1) (τ X0)
       grind)
    | exact resolve eq841 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq7528 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7521 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq7521
    | (have j0 := eq7521 X0 X1
       grind)
    | exact resolve eq7521 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7521
  have eq7538 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7528 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq7528
    | (have j0 := eq7528 X0 X1
       grind)
    | exact resolve eq7528 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7528
  have eq7547 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7538 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7538
    | (have j0 := eq7538 X0 X1
       grind)
    | exact resolve eq7538 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7538
  have eq7548 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7547 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7547
    | (have j0 := eq7547 X0 X1
       grind)
    | exact resolve eq7547 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7547
  have eq12502 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq817
       have i₂ := eq12 y x
       grind)
    | exact superpose eq12 eq817
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq817 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq12503 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12502
  have eq12556 : ∀ X0 X1 : G, (k X0 (M.op (σ x) X1)) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq297 (σ x) (σ y) X1 X0
       have i₂ := eq12503
       grind)
    | exact superpose eq12503 eq297
    | exact resolve eq297 eq12503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15805 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12556 X0 (σ y)
       have i₂ := eq12503
       grind)
    | exact superpose eq12503 eq12556
    | exact resolve eq12556 eq12503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12503 eq12556
  have eq15840 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq15805 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15805
  have eq16352 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq40 X0 (σ x)
       have i₂ := eq15840 (σ X0)
       grind)
    | exact superpose eq15840 eq40
    | exact resolve eq40 eq15840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq15840
  have eq16357 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16352 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq16352
    | exact resolve eq16352 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16352
  have eq16360 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16357 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq16357
    | exact resolve eq16357 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16357
  have eq16877 : ∀ X0 : G, x ≠ X0 ∨ x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7548 X0 x
       have i₂ := eq16360 X0
       grind)
    | exact superpose eq16360 eq7548
    | (have j0 := eq7548 X0 x
       grind)
    | (have r₁ := eq7548 x x
       have r₂ := eq16360 x
       grind)
    | exact resolve eq7548 eq16360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16360
  have eq21818 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have j0 := eq16877 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16877
  have eq22586 : ∀ X0 X1 : G, (k X0 (M.op x X1)) = X0 ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq297 x y X1 X0
       have i₂ := eq21818
       grind)
    | exact superpose eq21818 eq297
    | exact resolve eq297 eq21818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq22771 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq22586 X0 y
       have i₂ := eq21818
       grind)
    | exact superpose eq21818 eq22586
    | exact resolve eq22586 eq21818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21818 eq22586
  have eq22822 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq22771 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22771
  have eq22972 : ∀ X0 : G, x ≠ X0 ∨ x = (M.op x X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq7548 X0 x
       have i₂ := eq22822 X0
       grind)
    | exact superpose eq22822 eq7548
    | (have j0 := eq7548 X0 x
       grind)
    | (have r₁ := eq7548 x x
       have r₂ := eq22822 x
       grind)
    | exact resolve eq7548 eq22822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7548 eq22822
  have eq36435 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have j0 := eq22972 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22972
  have eq36436 : x = (M.op x x) := by grind
  clear eq36435
  have eq37788 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq36436
       grind)
    | exact superpose eq36436 eq11
    | (have j0 := eq11 x x
       grind)
    | (have r₁ := eq11 x x
       have r₂ := eq36436
       grind)
    | exact resolve eq11 eq36436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37810 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 x x X0 X1
       have i₂ := eq36436
       grind)
    | exact superpose eq36436 eq95
    | exact resolve eq95 eq36436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq37895 : x = (k x x) := by grind
  clear eq37788
  have eq37913 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq37810 X0 X1
       have i₂ := eq36436
       grind)
    | exact superpose eq36436 eq37810
    | exact resolve eq37810 eq36436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37810
  have eq39335 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq841 x x
       have i₂ := eq37895
       grind)
    | exact superpose eq37895 eq841
    | (have j0 := eq841 x x
       grind)
    | exact resolve eq841 eq37895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841 eq37895
  have eq39339 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq39335
  have eq54212 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq23 (σ x) X0 (σ x)
       have i₂ := eq39339
       grind)
    | exact superpose eq39339 eq23
    | exact resolve eq23 eq39339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq54309 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 (M.op X3 (M.op (σ x) (σ x))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1698 X3 (σ x) (σ x) X0 X2 X1
       have i₂ := eq39339
       grind)
    | exact superpose eq39339 eq1698
    | exact resolve eq1698 eq39339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1698
  have eq54310 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X3) X4))) = (M.op X0 (M.op (σ x) (σ x))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1764 X1 X2 X3 X4 X0 (σ x) (σ x)
       have i₂ := eq39339
       grind)
    | exact superpose eq39339 eq1764
    | exact resolve eq1764 eq39339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1764
  have eq54342 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X3) X4))) = (M.op X0 (σ x)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq54310 X0 X1 X2 X3 X4
       have i₂ := eq39339
       grind)
    | exact superpose eq39339 eq54310
    | exact resolve eq54310 eq39339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54310
  have eq54343 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 (M.op X3 (σ x)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54309 X0 X1 X2 X3
       have i₂ := eq39339
       grind)
    | exact superpose eq39339 eq54309
    | exact resolve eq54309 eq39339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54309
  have eq54367 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq54212 X0
       have i₂ := eq39339
       grind)
    | exact superpose eq39339 eq54212
    | exact resolve eq54212 eq39339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39339 eq54212
  have eq54385 : ∀ X0 X2 X3 : G, (M.op X0 x) = (M.op X0 (M.op X2 (M.op X3 (σ x)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq54343 X0 x X2 X3
       have i₂ := eq37913 X0 x
       grind)
    | exact superpose eq37913 eq54343
    | exact resolve eq54343 eq37913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54343
  have eq54397 : (σ x) = (M.op (σ x) x) := by
    first
    | (have i₁ := eq54367 x
       have i₂ := eq37913 (σ x) x
       grind)
    | exact superpose eq37913 eq54367
    | exact resolve eq54367 eq37913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37913 eq54367
  have eq54536 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op x X0) = (M.op x (M.op X1 (M.op X2 (M.op X3 (M.op (M.op X4 X5) X6))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq3567 X2 X3 X4 X5 X6 x x X0 X1
       have i₂ := eq36436
       grind)
    | exact superpose eq36436 eq3567
    | exact resolve eq3567 eq36436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3567
  have eq56227 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op x (M.op X1 (M.op X2 (σ x)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54536 X0 X1 X2 x x x x
       have i₂ := eq54342 X2 x x x x
       grind)
    | exact superpose eq54342 eq54536
    | exact resolve eq54536 eq54342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54342 eq54536
  have eq56284 : ∀ X0 : G, (M.op x X0) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq56227 X0 x x
       have i₂ := eq54385 x x x
       grind)
    | exact superpose eq54385 eq56227
    | exact resolve eq56227 eq54385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54385 eq56227
  have eq56327 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq56284 X0
       have i₂ := eq36436
       grind)
    | exact superpose eq36436 eq56284
    | exact resolve eq56284 eq36436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36436 eq56284
  have eq56701 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq155 x x x X0 X1 X2 x
       have i₂ := eq56327 (M.op (M.op x x) x)
       grind)
    | exact superpose eq56327 eq155
    | exact resolve eq155 eq56327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq102333 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq56701 (σ x) x x
       have i₂ := eq54397
       grind)
    | exact superpose eq54397 eq56701
    | exact resolve eq56701 eq54397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54397 eq56701
  have eq103992 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq102333 (σ y)
       grind)
    | exact superpose eq102333 eq14
    | exact resolve eq14 eq102333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102333
  have eq104609 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq103992
       have i₂ := eq56327 y
       grind)
    | exact superpose eq56327 eq103992
    | exact resolve eq103992 eq56327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56327 eq103992
  have eq104610 : False := by grind
  exact eq104610

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

/-- `Equation4447`: `x ◇ (y ◇ x) = (y ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pxy_Equation4447 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4447 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4447.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X1) X2) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X3) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X1 X1) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | (have i₁ := eq8 (M.op X1 X0) X0 X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X2 X1 x
       grind)
    | (have i₁ := eq8 X0 X1 (M.op X1 (M.op X1 X1))
       have i₂ := eq8 (M.op X1 X1) X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X0 (M.op X3 X3))
       have i₂ := eq8 (M.op X3 X3) X0 X1
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq37 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq32 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq44 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq117 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 (M.op X3 (M.op X1 X1))
       have i₂ := eq22 (M.op X1 X1) X3 X2
       grind)
    | (have i₁ := eq8 X0 X1 (M.op X3 (M.op X1 X1))
       have i₂ := eq22 X2 X3 (M.op X1 X1)
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq153 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X2) X3) = (M.op X4 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq23 X2 X3 X4 (M.op X1 X1)
       have i₂ := eq8 X0 X1 X4
       grind)
    | (have i₁ := eq23 X0 X1 (M.op X1 X0) X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq23
    | exact resolve eq23 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq204 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (M.op X2 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq37 X1 (σ X0) X2
       grind)
    | exact superpose eq37 eq44
    | (have j1 := eq37 X1 X1 X2
       grind)
    | exact resolve eq44 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq212 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq37 X1 X2 (τ X0)
       grind)
    | exact superpose eq37 eq15
    | (have j1 := eq37 X1 X2 X2
       grind)
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq37
  have eq218 : ∀ X0 X1 X2 : G, (k X0 (τ X1)) = X0 ∨ (M.op X2 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq204 X0 X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq204
    | (have j0 := eq204 X0 X1 X2
       grind)
    | exact resolve eq204 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq1426 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq35 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq2962 : ∀ X0 X1 X2 X3 X5 X6 : G, (M.op X0 (M.op X1 (M.op X2 X1))) = (M.op X5 (M.op X6 (M.op X3 X6))) := by
    intro X0 X1 X2 X3 X5 X6
    first
    | (have i₁ := eq18 X6 X3 X5 x
       have i₂ := eq153 X1 X2 (M.op X3 X3) x X0
       grind)
    | (have i₁ := eq18 X0 X1 X2 (M.op X0 (M.op X1 X0))
       have i₂ := eq153 X0 X1 X2 X3 (M.op (M.op X1 X1) (M.op X1 X1))
       grind)
    | exact superpose eq153 eq18
    | exact resolve eq18 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq153
  have eq11584 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 (τ (σ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq218 X2 (σ X1) (σ X0)
       grind)
    | exact superpose eq218 eq13
    | (have j1 := eq218 X2 (σ X1) X2
       grind)
    | exact resolve eq13 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq11600 : ∀ X0 X1 X2 : G, (k X2 X1) = X2 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11584 X0 X1 X2
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq11584
    | (have j0 := eq11584 X0 X1 X2
       grind)
    | exact resolve eq11584 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11584
  have eq14357 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq212 (σ X0) X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq212
    | (have j0 := eq212 X0 X1 X2
       grind)
    | exact resolve eq212 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq14474 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14357 X0 X1 X2
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq14357
    | (have j0 := eq14357 X0 X1 X2
       grind)
    | exact resolve eq14357 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14357
  have eq22509 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1426 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq1426
    | (have j0 := eq1426 (τ X0)
       grind)
    | exact resolve eq1426 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq22547 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq22509 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22509
    | (have j0 := eq22509 X0
       grind)
    | exact resolve eq22509 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22509
  have eq22562 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq22547 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22547
    | (have j0 := eq22547 X0
       grind)
    | exact resolve eq22547 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22547
  have eq362281 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq11600 x y X0
       grind)
    | exact superpose eq11600 eq14
    | (have j1 := eq11600 X0 y X0
       grind)
    | exact resolve eq14 eq11600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11600
  have eq362340 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq362281 X0
       have j1 := eq14474 X0 y X0
       grind)
    | (have r₁ := eq362281 X0
       have r₂ := eq14474 x y x
       grind)
    | exact resolve eq362281 eq14474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14474 eq362281
  have eq362657 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1426 y
       have i₂ := eq362340 y
       grind)
    | exact superpose eq362340 eq1426
    | (have j0 := eq1426 y
       grind)
    | exact resolve eq1426 eq362340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426
  have eq362661 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq22562 y
       have i₂ := eq362340 y
       grind)
    | exact superpose eq362340 eq22562
    | (have j0 := eq22562 y
       grind)
    | (have r₁ := eq22562 y
       have r₂ := eq362340 y
       grind)
    | exact resolve eq22562 eq362340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22562 eq362340
  have eq362727 : y = (M.op y y) := by grind
  clear eq362661
  have eq362731 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq362657
  have eq366350 : ∀ X0 : G, (M.op y y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq8 y y x
       have i₂ := eq362727
       grind)
    | exact superpose eq362727 eq8
    | exact resolve eq8 eq362727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366369 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq117 X0 X1 y y
       have i₂ := eq362727
       grind)
    | exact superpose eq362727 eq117
    | exact resolve eq117 eq362727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366584 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = y := by
    intro X0 X1
    first
    | (have i₁ := eq366369 X0 X1
       have i₂ := eq362727
       grind)
    | exact superpose eq362727 eq366369
    | exact resolve eq366369 eq362727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366369
  have eq366592 : ∀ X0 : G, y = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq366350 X0
       have i₂ := eq362727
       grind)
    | exact superpose eq362727 eq366350
    | exact resolve eq366350 eq362727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362727 eq366350
  have eq375192 : ∀ X0 X1 X2 : G, y = (M.op X0 (M.op X1 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2962 X0 X1 X2 x y x
       have i₂ := eq366592 (M.op x (M.op x x))
       grind)
    | exact superpose eq366592 eq2962
    | exact resolve eq2962 eq366592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2962 eq366592
  have eq375241 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq375192 X0 x x
       have i₂ := eq366584 x x
       grind)
    | exact superpose eq366584 eq375192
    | exact resolve eq375192 eq366584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375192
  have eq415304 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ y) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq117 X0 X1 (σ y) (σ y)
       have i₂ := eq362731
       grind)
    | exact superpose eq362731 eq117
    | exact resolve eq117 eq362731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq415484 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq415304 X0 X1
       have i₂ := eq362731
       grind)
    | exact superpose eq362731 eq415304
    | exact resolve eq415304 eq362731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362731 eq415304
  have eq415648 : y = (σ y) := by
    first
    | (have i₁ := eq415484 x x
       have i₂ := eq366584 x x
       grind)
    | exact superpose eq366584 eq415484
    | exact resolve eq415484 eq366584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366584 eq415484
  have eq415745 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq415648
       grind)
    | exact superpose eq415648 eq14
    | exact resolve eq14 eq415648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq415811 : y ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq415745
       have i₂ := eq375241 (σ x)
       grind)
    | exact superpose eq375241 eq415745
    | exact resolve eq415745 eq375241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415745
  have eq415832 : y ≠ (σ y) := by
    first
    | (have i₁ := eq415811
       have i₂ := eq375241 x
       grind)
    | exact superpose eq375241 eq415811
    | exact resolve eq415811 eq375241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375241 eq415811
  have eq415837 : False := by grind
  exact eq415837

/-- `Equation4449`: `x ◇ (y ◇ x) = (y ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pxx_pxy_Equation4449 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4449 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4449.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X2) X1) := by
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
  have eq19 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k (τ X0) X1) X2
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X0 X2) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X0 X2) X2 X3
       have i₂ := eq8 X2 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 x X0 X3
       have i₂ := eq8 x X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op (M.op X0 X1) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X0 X3)
       have i₂ := eq8 X3 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X2 X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
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
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq44 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X1)) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X0 X0
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
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
  have eq47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq48 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
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
  have eq51 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq46 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq73 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op (M.op X0 X1) X0) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X2 X3 (M.op X0 X2)
       have i₂ := eq8 X2 X0 X1
       grind)
    | exact superpose eq8 eq23
    | exact resolve eq23 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = (M.op X2 (M.op (M.op X1 X3) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq26 X2 (M.op X1 X3) X1
       have i₂ := eq8 X0 X1 X3
       grind)
    | exact superpose eq8 eq26
    | exact resolve eq26 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op X0 (M.op X1 X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X1 X3)
       have i₂ := eq26 X3 X1 X0
       grind)
    | (have i₁ := eq8 X2 X3 (M.op X1 X3)
       have i₂ := eq26 X0 X1 X3
       grind)
    | exact superpose eq26 eq8
    | exact resolve eq8 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X1 X2) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X1 X2) X2 X3
       have i₂ := eq26 X2 X1 X0
       grind)
    | (have i₁ := eq8 (M.op X1 X2) X2 X3
       have i₂ := eq26 X0 X1 X2
       grind)
    | exact superpose eq26 eq8
    | exact resolve eq8 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = (M.op (M.op (M.op X3 X4) X3) (M.op X0 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X3 X4 X0 (M.op X0 X2)
       have i₂ := eq23 X0 X2 X1
       grind)
    | (have i₁ := eq24 X3 X4 X0 (M.op X0 X2)
       have i₂ := eq23 X0 X1 X2
       grind)
    | exact superpose eq23 eq24
    | exact resolve eq24 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq136 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = (M.op (M.op (M.op X3 X4) X3) (M.op X1 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X3 X4 X1 (M.op X1 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq24
    | exact resolve eq24 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 X3)) = (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) X5) X4) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq24 X5 (M.op X2 X5) X3 X4
       have i₂ := eq24 X0 X1 X5 X2
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X1)) = (M.op (M.op X0 X0) X2) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X0 X0 X1 X2
       have i₂ := eq12 X3 X0
       grind)
    | exact superpose eq12 eq24
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X4 X3)) = (M.op (M.op (M.op (M.op X0 X1) X0) X2) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X3 X4 (M.op X2 X4)
       have i₂ := eq24 X0 X1 X4 X2
       grind)
    | exact superpose eq24 eq8
    | exact resolve eq8 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 (σ X1)) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq51 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq51 eq13
    | (have j1 := eq51 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq327 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X4) X3) = (M.op (M.op X5 X3) (M.op (M.op (M.op (M.op X0 X1) X0) X2) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq21 X5 (M.op X2 X5) X3 X4
       have i₂ := eq24 X0 X1 X5 X2
       grind)
    | exact superpose eq24 eq21
    | exact resolve eq21 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq24
  have eq780 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq222 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq936 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq780 (σ X0)
       grind)
    | exact superpose eq780 eq13
    | exact resolve eq13 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq947 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq936 X0
       have i₂ := eq780 X0
       grind)
    | exact superpose eq780 eq936
    | exact resolve eq936 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq1242 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ X0)
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq11
    | (have j0 := eq11 X1 (σ X0)
       have j1 := eq47 X0 X0
       grind)
    | (have r₁ := eq11 X0 (σ X1)
       have r₂ := eq47 X0 X1
       grind)
    | exact resolve eq11 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq1288 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1242 X0 X1
       have j1 := eq11 X1 (σ X0)
       grind)
    | (have r₁ := eq1242 X0 X1
       have r₂ := eq11 X0 (σ X0)
       grind)
    | exact resolve eq1242 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242
  have eq1322 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1288 X0 X1
       have i₂ := eq780 X0
       grind)
    | exact superpose eq780 eq1288
    | (have j0 := eq1288 X0 X1
       grind)
    | exact resolve eq1288 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288
  have eq2100 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
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
  have eq2210 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2100 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2100
    | (have j0 := eq2100 X0 X1
       grind)
    | exact resolve eq2100 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2100
  have eq5878 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1322 X0 X1
       have i₂ := eq2210 X2 X0
       grind)
    | exact superpose eq2210 eq1322
    | (have j0 := eq1322 X0 X1
       have j1 := eq2210 X2 X0
       grind)
    | exact resolve eq1322 eq2210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322
  have eq5900 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq5878 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5878
  have eq8061 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op X0 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq128 X0 (M.op X2 x) X2 X3
       have i₂ := eq135 X0 X1 (M.op (M.op X2 x) X0) X2 x
       grind)
    | exact superpose eq135 eq128
    | exact resolve eq128 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq135
  have eq8413 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X2 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8061 x x X0 X1
       have i₂ := eq8061 x x X2 X3
       grind)
    | exact superpose eq8061 eq8061
    | exact resolve eq8061 eq8061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8061
  have eq9146 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X2)) = (M.op X0 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X2 X0 (M.op (M.op x x) x)
       have i₂ := eq136 X1 X0 (M.op (M.op x x) x) x x
       grind)
    | exact superpose eq136 eq26
    | exact resolve eq26 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq10363 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X4 X5) X4) = (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) X3) X6) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq8413 X4 X5 X6 (M.op X3 X6)
       have i₂ := eq169 X0 X1 X2 X6 X3
       grind)
    | exact superpose eq169 eq8413
    | exact resolve eq8413 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq10587 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op X4 X5) X4) X2) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq73 X4 X5 X2 x
       have i₂ := eq8413 X2 x X0 X1
       grind)
    | (have i₁ := eq73 X4 X5 X2 x
       have i₂ := eq8413 X0 X1 X2 x
       grind)
    | exact superpose eq8413 eq73
    | exact resolve eq73 eq8413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10618 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq127 X3 x X2 X3
       have i₂ := eq8413 X3 (M.op x X3) X0 X1
       grind)
    | (have i₁ := eq127 X3 x X2 X3
       have i₂ := eq8413 X0 X1 X3 (M.op x X3)
       grind)
    | exact superpose eq8413 eq127
    | exact resolve eq127 eq8413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13395 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op X0 X0) X1) ∨ (M.op X4 X0) = (k X4 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq10618 X1 (M.op X0 X1) X2 X3
       have i₂ := eq44 X0 X1 X4
       grind)
    | exact superpose eq44 eq10618
    | (have j1 := eq44 X0 X1 X4
       grind)
    | exact resolve eq10618 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq13642 : ∀ X0 X1 X2 X4 X5 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (M.op X4 X5) X4) X2) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq73 X4 X5 X2 x
       have i₂ := eq10618 X2 x X0 X1
       grind)
    | exact superpose eq10618 eq73
    | exact resolve eq73 eq10618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq13681 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq127 X1 x X0 X1
       have i₂ := eq10618 X1 (M.op x X1) X2 X3
       grind)
    | exact superpose eq10618 eq127
    | exact resolve eq127 eq10618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq24381 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) X2) ≠ (M.op X0 (M.op (M.op X1 X1) X0)) ∨ (M.op (M.op X1 X1) X2) = (k (M.op X1 X1) X2) ∨ (k X3 X1) = (M.op X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq222 (M.op X1 X1) X2
       have i₂ := eq147 X1 X0 (M.op X1 X1) X3
       grind)
    | exact superpose eq147 eq222
    | (have j0 := eq222 (M.op X1 X1) X2
       have j1 := eq147 X2 X1 X2 (M.op X1 X1)
       grind)
    | (have r₁ := eq222 (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq147 X0 (M.op X0 X0) (M.op X0 X0) X3
       grind)
    | exact resolve eq222 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq222
  have eq24619 : ∀ X1 X2 X3 : G, (M.op (M.op X1 X1) X2) = (k (M.op X1 X1) X2) ∨ (k X3 X1) = (M.op X3 X1) := by
    intro X1 X2 X3
    first
    | (have j0 := eq24381 x X1 X2 X3
       have j1 := eq13395 X2 X1 X2 X3 (M.op X1 X1)
       grind)
    | (have r₁ := eq24381 (M.op x x) X1 (M.op X3 (M.op X1 X1)) X3
       have r₂ := eq13395 x (M.op (M.op X1 X1) (M.op x x)) (M.op X1 X1) X3 x
       grind)
    | (have r₁ := eq24381 X2 x X1 X3
       have r₂ := eq13395 x X1 X2 (M.op x x) x
       grind)
    | exact resolve eq24381 eq13395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13395 eq24381
  have eq33218 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq216 x y X0
       grind)
    | exact superpose eq216 eq14
    | (have j1 := eq216 X0 y X0
       grind)
    | exact resolve eq14 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq33676 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq33218 X0
       have j1 := eq5900 y X0 x
       grind)
    | (have r₁ := eq33218 X0
       have r₂ := eq5900 y x x
       grind)
    | exact resolve eq33218 eq5900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5900 eq33218
  have eq33904 : ∀ X0 : G, (k X0 (σ y)) ≠ (k X0 (σ y)) ∨ (k X0 X0) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq223 X0 X0
       have i₂ := eq33676 X0
       grind)
    | exact superpose eq33676 eq223
    | exact resolve eq223 eq33676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33929 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (M.op X0 (k X0 (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq9146 X0 X1 X0
       have i₂ := eq33676 X0
       grind)
    | exact superpose eq33676 eq9146
    | exact resolve eq9146 eq33676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9146
  have eq33990 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq947 X0
       have i₂ := eq33676 (σ X0)
       grind)
    | exact superpose eq33676 eq947
    | exact resolve eq947 eq33676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq34029 : ∀ X0 : G, (k X0 X0) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq33904 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33904
  have eq34052 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq33990 X0
       have i₂ := eq13 X0 y
       grind)
    | exact superpose eq13 eq33990
    | exact resolve eq33990 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33990
  have eq34813 : ∀ X0 X1 : G, (σ (k (k X0 (τ (σ X0))) X1)) = (k (k (σ X0) (σ y)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (σ X0) X1
       have i₂ := eq34029 (σ X0)
       grind)
    | (have i₁ := eq31 X0 (σ y) x
       have i₂ := eq34029 (σ X0)
       grind)
    | exact superpose eq34029 eq31
    | exact resolve eq31 eq34029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq34815 : ∀ X0 : G, (k X0 (τ (σ X0))) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq32 X0 (σ X0)
       have i₂ := eq34029 (σ X0)
       grind)
    | (have i₁ := eq32 X0 (σ y)
       have i₂ := eq34029 (σ X0)
       grind)
    | exact superpose eq34029 eq32
    | exact resolve eq32 eq34029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34875 : ∀ X0 : G, (k X0 (τ (σ X0))) = (k (τ (σ X0)) y) := by
    intro X0
    first
    | (have i₁ := eq34815 X0
       have i₂ := eq20 (σ X0) y
       grind)
    | exact superpose eq20 eq34815
    | exact resolve eq34815 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq34815
  have eq34877 : ∀ X0 X1 : G, (σ (k (k X0 (τ (σ X0))) X1)) = (σ (k (k (τ (σ X0)) y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34813 X0 X1
       have i₂ := eq19 (σ X0) y X1
       grind)
    | exact superpose eq19 eq34813
    | exact resolve eq34813 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34813
  have eq34915 : ∀ X0 : G, (k X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq34875 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq34875
    | exact resolve eq34875 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34875
  have eq34917 : ∀ X0 X1 : G, (σ (k (k X0 X0) X1)) = (σ (k (k X0 y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34877 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq34877
    | exact resolve eq34877 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34877
  have eq34946 : ∀ X0 X1 : G, (σ (k (M.op X0 X0) X1)) = (σ (k (k X0 y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34917 X0 X1
       have i₂ := eq780 X0
       grind)
    | exact superpose eq780 eq34917
    | exact resolve eq34917 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34917
  have eq35960 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq780 X0
       have i₂ := eq34915 X0
       grind)
    | (have i₁ := eq780 y
       have i₂ := eq34915 y
       grind)
    | exact superpose eq34915 eq780
    | exact resolve eq780 eq34915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35967 : ∀ X0 : G, (k X0 (σ y)) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq34029 X0
       have i₂ := eq34915 X0
       grind)
    | (have i₁ := eq34029 y
       have i₂ := eq34915 y
       grind)
    | exact superpose eq34915 eq34029
    | exact resolve eq34029 eq34915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34029
  have eq36002 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ X0) y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq34915 (σ X0)
       grind)
    | exact superpose eq34915 eq13
    | exact resolve eq13 eq34915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36027 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq2210 X0 y
       have i₂ := eq34915 X0
       grind)
    | (have i₁ := eq2210 X0 X0
       have i₂ := eq34915 X0
       grind)
    | exact superpose eq34915 eq2210
    | (have j0 := eq2210 X0 y
       grind)
    | exact resolve eq2210 eq34915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2210 eq34915
  have eq36028 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (M.op X0 y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq36027 X0
       have i₂ := eq780 X0
       grind)
    | exact superpose eq780 eq36027
    | exact resolve eq36027 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36027
  have eq36051 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) y) := by
    intro X0
    first
    | (have i₁ := eq36002 X0
       have i₂ := eq780 X0
       grind)
    | exact superpose eq780 eq36002
    | exact resolve eq36002 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36002
  have eq37175 : ∀ X0 X1 : G, (k X0 y) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq35960 X0
       grind)
    | exact superpose eq35960 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq35960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37258 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op X1 X2) X1) X3) X4) X0) = (M.op X0 (k X0 y)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq143 X1 X2 X3 X0 X0 X4
       have i₂ := eq35960 X0
       grind)
    | exact superpose eq35960 eq143
    | exact resolve eq143 eq35960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq37305 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = (M.op (k X0 y) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8413 X1 X2 X0 X0
       have i₂ := eq35960 X0
       grind)
    | exact superpose eq35960 eq8413
    | exact resolve eq8413 eq35960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37325 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op X0 (k X0 y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13681 X1 X2 X0 X0
       have i₂ := eq35960 X0
       grind)
    | exact superpose eq35960 eq13681
    | exact resolve eq13681 eq35960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13681
  have eq37340 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op (M.op X0 X1) X2))) = (k (M.op (M.op X0 X1) X0) y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq136 X2 (M.op X0 X1) X0 X0 X1
       have i₂ := eq35960 (M.op (M.op X0 X1) X0)
       grind)
    | exact superpose eq35960 eq136
    | exact resolve eq136 eq35960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq37364 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 X2))) = (M.op (M.op X0 X1) (k (M.op X0 X1) y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq115 X2 X0 (M.op X0 X1) X1
       have i₂ := eq35960 (M.op X0 X1)
       grind)
    | exact superpose eq35960 eq115
    | exact resolve eq115 eq35960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq35960
  have eq37414 : ∀ X0 X1 : G, (M.op X0 (k X0 (σ y))) = (M.op (M.op X0 X1) (k (M.op X0 X1) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq37364 X0 X1 x
       have i₂ := eq33929 X0 x
       grind)
    | exact superpose eq33929 eq37364
    | exact resolve eq37364 eq33929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37364
  have eq37417 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (k (M.op X0 X1) (σ y))) = (k (M.op (M.op X0 X1) X0) y) := by
    intro X0 X1
    first
    | (have i₁ := eq37340 X0 X1 x
       have i₂ := eq33929 (M.op X0 X1) x
       grind)
    | exact superpose eq33929 eq37340
    | exact resolve eq37340 eq33929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33929 eq37340
  have eq37434 : ∀ X0 X1 : G, (M.op X0 (k X0 y)) = (M.op (M.op X0 X1) (k (M.op X0 X1) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq37414 X0 X1
       have i₂ := eq35967 X0
       grind)
    | exact superpose eq35967 eq37414
    | exact resolve eq37414 eq35967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37414
  have eq37437 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X0) y) = (M.op (M.op X0 X1) (k (M.op X0 X1) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq37417 X0 X1
       have i₂ := eq35967 (M.op X0 X1)
       grind)
    | exact superpose eq35967 eq37417
    | exact resolve eq37417 eq35967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37417
  have eq37449 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X0) y) = (M.op X0 (k X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq37437 X0 X1
       have i₂ := eq37434 X0 X1
       grind)
    | exact superpose eq37434 eq37437
    | exact resolve eq37437 eq37434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37437
  have eq39314 : ∀ X0 : G, (k X0 (τ (σ y))) = (τ (k (σ X0) y)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 (σ y)
       have i₂ := eq35967 (σ X0)
       grind)
    | exact superpose eq35967 eq32
    | exact resolve eq32 eq35967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39316 : ∀ X0 X1 : G, (σ (k (k (τ X0) X1) y)) = (k (k X0 (σ X1)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1 y
       have i₂ := eq35967 (k X0 (σ X1))
       grind)
    | exact superpose eq35967 eq19
    | exact resolve eq19 eq35967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq39321 : ∀ X0 : G, (k X0 (τ (σ y))) = (k X0 (τ y)) := by
    intro X0
    first
    | (have i₁ := eq39314 X0
       have i₂ := eq32 X0 y
       grind)
    | exact superpose eq32 eq39314
    | exact resolve eq39314 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39314
  have eq39340 : ∀ X0 : G, (k X0 y) = (k X0 (τ y)) := by
    intro X0
    first
    | (have i₁ := eq39321 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq39321
    | exact resolve eq39321 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39321
  have eq52893 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) X3) (M.op (M.op (M.op X0 X1) X0) X2)) ≠ (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2)) X4) ∨ (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) X3) (M.op (M.op (M.op X0 X1) X0) X2)) = (k (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq223 (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2)) X1
       have i₂ := eq327 X0 X1 X2 (M.op (M.op (M.op X0 X1) X0) X2) X4 (M.op (M.op (M.op X0 X1) X0) X2)
       grind)
    | exact superpose eq327 eq223
    | (have r₁ := eq223 (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2)) (M.op (M.op (M.op X0 X1) X0) X2)
       have r₂ := eq327 X0 X1 X2 (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2)
       grind)
    | exact resolve eq223 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223 eq327
  have eq53084 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) X3) (M.op (M.op (M.op X0 X1) X0) X2)) = (k (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq52893 X0 X1 X2 X3 X4
       grind)
    | (have r₁ := eq52893 X0 X1 X2 x x
       have r₂ := eq10363 X0 X1 X2 (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2) x x
       grind)
    | (have r₁ := eq52893 X0 X1 X2 X3 (M.op (M.op (M.op X0 X1) X0) X2)
       have r₂ := eq10363 X0 X1 X2 X3 (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2)
       grind)
    | exact resolve eq52893 eq10363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10363 eq52893
  have eq53212 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) X3) (M.op (M.op (M.op X0 X1) X0) X2)) = (k (k (M.op (M.op (M.op X0 X1) X0) X2) (σ y)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53084 X0 X1 X2 X3 X4
       have i₂ := eq33676 (M.op (M.op (M.op X0 X1) X0) X2)
       grind)
    | exact superpose eq33676 eq53084
    | exact resolve eq53084 eq33676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53084
  have eq53308 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) X3) (M.op (M.op (M.op X0 X1) X0) X2)) = (k (k (M.op (M.op (M.op X0 X1) X0) X2) y) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53212 X0 X1 X2 X3 X4
       have i₂ := eq35967 (M.op (M.op (M.op X0 X1) X0) X2)
       grind)
    | exact superpose eq35967 eq53212
    | exact resolve eq53212 eq35967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53212
  have eq53352 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) (k (M.op (M.op (M.op X0 X1) X0) X2) y)) = (k (k (M.op (M.op (M.op X0 X1) X0) X2) y) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq53308 X0 X1 X2 x X4
       have i₂ := eq37258 (M.op (M.op (M.op X0 X1) X0) X2) X0 X1 X2 x
       grind)
    | exact superpose eq37258 eq53308
    | exact resolve eq53308 eq37258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37258 eq53308
  have eq53386 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op X0 X1) X0) (k (M.op (M.op X0 X1) X0) y)) = (k (k (M.op (M.op (M.op X0 X1) X0) X2) y) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq53352 X0 X1 X2 X4
       have i₂ := eq37434 (M.op (M.op X0 X1) X0) X2
       grind)
    | exact superpose eq37434 eq53352
    | exact resolve eq53352 eq37434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53352
  have eq53415 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) (k (M.op X0 X1) y)) = (k (k (M.op (M.op (M.op X0 X1) X0) X2) y) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq53386 X0 X1 X2 X4
       have i₂ := eq37434 (M.op X0 X1) X0
       grind)
    | exact superpose eq37434 eq53386
    | exact resolve eq53386 eq37434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53386
  have eq53444 : ∀ X0 X1 X2 X4 : G, (M.op X0 (k X0 y)) = (k (k (M.op (M.op (M.op X0 X1) X0) X2) y) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq53415 X0 X1 X2 X4
       have i₂ := eq37434 X0 X1
       grind)
    | exact superpose eq37434 eq53415
    | exact resolve eq53415 eq37434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37434 eq53415
  have eq104375 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X0)) = (M.op X3 (k X3 y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq37325 X3 X2 (k X2 y)
       have i₂ := eq37305 X2 X0 X1
       grind)
    | exact superpose eq37305 eq37325
    | exact resolve eq37325 eq37305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37305 eq37325
  have eq159849 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ y)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 y
       have i₂ := eq37175 (σ X0) X1
       grind)
    | exact superpose eq37175 eq32
    | (have j1 := eq37175 (σ X0) X1
       grind)
    | exact resolve eq32 eq37175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq37175
  have eq159962 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 y) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq159849 X0 X1
       have i₂ := eq39340 X0
       grind)
    | exact superpose eq39340 eq159849
    | (have j0 := eq159849 X0 X1
       grind)
    | exact resolve eq159849 eq39340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159849
  have eq159995 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (k X0 y) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq159962 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq159962
    | (have j0 := eq159962 X0 X1
       grind)
    | exact resolve eq159962 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159962
  have eq212590 : ∀ X0 X1 X2 X3 : G, (σ (M.op (M.op X0 X1) X0)) = (σ (k (M.op (M.op X2 X3) X2) y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq34052 (M.op (M.op X2 X3) X2)
       have i₂ := eq10587 X0 X1 (M.op (M.op X2 X3) X2) X2 X3
       grind)
    | exact superpose eq10587 eq34052
    | exact resolve eq34052 eq10587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10587 eq34052
  have eq212784 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) X0)) = (σ (M.op X2 (k X2 y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq212590 X0 X1 X2 x
       have i₂ := eq37449 X2 x
       grind)
    | exact superpose eq37449 eq212590
    | exact resolve eq212590 eq37449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37449 eq212590
  have eq267879 : ∀ X0 X1 : G, (k (k X0 y) X1) = (τ (σ (k (M.op X0 X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (k X0 y) X1)
       have i₂ := eq34946 X0 X1
       grind)
    | exact superpose eq34946 eq9
    | exact resolve eq9 eq34946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34946
  have eq267882 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (k (k X0 y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq267879 X0 X1
       have i₂ := eq9 (k (M.op X0 X0) X1)
       grind)
    | exact superpose eq9 eq267879
    | exact resolve eq267879 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267879
  have eq383077 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 (M.op X1 X0))) = (σ (M.op (M.op X2 X3) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq212784 X2 X3 (M.op (M.op x x) x)
       have i₂ := eq13642 X0 X1 (k (M.op (M.op x x) x) y) x x
       grind)
    | exact superpose eq13642 eq212784
    | exact resolve eq212784 eq13642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13642 eq212784
  have eq466117 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq24619 X0 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24619
  have eq466118 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq466117 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466117
  have eq466138 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (k X0 y) X0) := by
    intro X0
    first
    | (have i₁ := eq267882 X0 X0
       have i₂ := eq466118 X0
       grind)
    | exact superpose eq466118 eq267882
    | exact resolve eq267882 eq466118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267882
  have eq466324 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = (k (k X0 y) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8413 X1 X2 X0 X0
       have i₂ := eq466138 X0
       grind)
    | exact superpose eq466138 eq8413
    | exact resolve eq8413 eq466138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8413
  have eq466343 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (k (k X0 y) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10618 X0 X0 X1 X2
       have i₂ := eq466138 X0
       grind)
    | exact superpose eq466138 eq10618
    | exact resolve eq10618 eq466138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10618 eq466138
  have eq467838 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k (k (τ y) y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq39340 (k (τ y) y)
       have i₂ := eq466324 (τ y) X0 X1
       grind)
    | exact superpose eq466324 eq39340
    | exact resolve eq39340 eq466324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39340 eq466324
  have eq469313 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 X0))) = (k (σ (k (τ X2) y)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (k (τ X2) y)
       have i₂ := eq466343 (τ X2) X0 X1
       grind)
    | exact superpose eq466343 eq16
    | exact resolve eq16 eq466343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq466343
  have eq469353 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 X0))) = (k (k X2 (σ y)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq469313 X0 X1 X2
       have i₂ := eq15 X2 y
       grind)
    | exact superpose eq15 eq469313
    | exact resolve eq469313 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq469313
  have eq469745 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 X0))) = (k (k X2 y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq469353 X0 X1 X2
       have i₂ := eq35967 X2
       grind)
    | exact superpose eq35967 eq469353
    | exact resolve eq469353 eq35967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469353
  have eq480276 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 X0))) = (σ (k (k (τ y) y) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq383077 X0 X1 x x
       have i₂ := eq467838 x x
       grind)
    | exact superpose eq467838 eq383077
    | exact resolve eq383077 eq467838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383077 eq467838
  have eq480441 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 X0))) = (k (k y (σ y)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq480276 X0 X1
       have i₂ := eq39316 y y
       grind)
    | exact superpose eq39316 eq480276
    | exact resolve eq480276 eq39316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39316 eq480276
  have eq480508 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 X0))) = (k (M.op y y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq480441 X0 X1
       have i₂ := eq33676 y
       grind)
    | exact superpose eq33676 eq480441
    | exact resolve eq480441 eq33676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33676 eq480441
  have eq480535 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 X0))) = (M.op (M.op y y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq480508 X0 X1
       have i₂ := eq466118 y
       grind)
    | exact superpose eq466118 eq480508
    | exact resolve eq480508 eq466118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466118 eq480508
  have eq485800 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 X0))) = (M.op X2 (k X2 y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53444 X2 x x (M.op (M.op (M.op X2 x) X2) x)
       have i₂ := eq469745 X0 X1 (M.op (M.op (M.op X2 x) X2) x)
       grind)
    | exact superpose eq469745 eq53444
    | exact resolve eq53444 eq469745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53444 eq469745
  have eq672449 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 y) ∨ y = (k y y) := by
    intro X0
    first
    | (have i₁ := eq35967 X0
       have i₂ := eq159995 y X0
       grind)
    | exact superpose eq159995 eq35967
    | (have j1 := eq159995 y x
       grind)
    | exact resolve eq35967 eq159995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35967 eq159995
  have eq672454 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq672449 X0
       have i₂ := eq780 y
       grind)
    | exact superpose eq780 eq672449
    | (have j0 := eq672449 X0
       grind)
    | exact resolve eq672449 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780 eq672449
  have eq672467 : (σ (M.op x y)) ≠ (k (σ x) y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq672454 (σ x)
       grind)
    | exact superpose eq672454 eq14
    | exact resolve eq14 eq672454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672454
  have eq672468 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq672467
       have i₂ := eq36051 x
       grind)
    | exact superpose eq36051 eq672467
    | exact resolve eq672467 eq36051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36051 eq672467
  have eq672469 : y = (M.op y y) := by
    first
    | (have r₁ := eq672468
       have r₂ := eq36028 x
       grind)
    | exact resolve eq672468 eq36028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36028 eq672468
  have eq672898 : ∀ X0 X1 : G, (M.op X1 (k X1 y)) = (M.op X0 (M.op y y)) := by
    intro X0 X1
    first
    | (have i₁ := eq104375 y y X0 X1
       have i₂ := eq672469
       grind)
    | exact superpose eq672469 eq104375
    | exact resolve eq104375 eq672469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104375
  have eq672974 : (M.op y y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq480535 y y
       have i₂ := eq672469
       grind)
    | exact superpose eq672469 eq480535
    | exact resolve eq480535 eq672469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480535
  have eq672988 : ∀ X0 : G, (σ (M.op y y)) = (M.op X0 (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq485800 y y X0
       have i₂ := eq672469
       grind)
    | exact superpose eq672469 eq485800
    | exact resolve eq485800 eq672469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485800
  have eq673005 : ∀ X0 : G, (σ y) = (M.op X0 (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq672988 X0
       have i₂ := eq672469
       grind)
    | exact superpose eq672469 eq672988
    | exact resolve eq672988 eq672469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672988
  have eq673019 : y = (σ y) := by
    first
    | (have i₁ := eq672974
       have i₂ := eq672469
       grind)
    | exact superpose eq672469 eq672974
    | exact resolve eq672974 eq672469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672974
  have eq673090 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 (k X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq672898 X0 X1
       have i₂ := eq672469
       grind)
    | exact superpose eq672469 eq672898
    | exact resolve eq672898 eq672469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672469 eq672898
  have eq673392 : ∀ X0 : G, (σ y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq673090 X0 x
       have i₂ := eq673005 x
       grind)
    | exact superpose eq673005 eq673090
    | exact resolve eq673090 eq673005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673005 eq673090
  have eq673573 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq673392 X0
       have i₂ := eq673019
       grind)
    | exact superpose eq673019 eq673392
    | exact resolve eq673392 eq673019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673392
  have eq673778 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq673019
       grind)
    | exact superpose eq673019 eq14
    | exact resolve eq14 eq673019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq673947 : y ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq673778
       have i₂ := eq673573 (σ x)
       grind)
    | exact superpose eq673573 eq673778
    | exact resolve eq673778 eq673573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673778
  have eq673969 : y ≠ (σ y) := by
    first
    | (have i₁ := eq673947
       have i₂ := eq673573 x
       grind)
    | exact superpose eq673573 eq673947
    | exact resolve eq673947 eq673573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673573 eq673947
  have eq673980 : False := by grind
  exact eq673980

/-- `Equation4461`: `x ◇ (y ◇ x) = (z ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pyy_pxy_Equation4461 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law4461 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4461.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X2) X1) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X2 X2)) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 (M.op X2 X2) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 x X1 X3
       have i₂ := eq8 x X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X2 X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X1)) = (M.op X0 X2) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 X3
       have i₂ := eq12 X3 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X2 X2)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq60 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    grind
  have eq63 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (k X0 (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    grind
  have eq107 : ∀ X0 X1 : G, (k X1 (M.op X1 X1)) = (M.op (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1
    grind
  have eq141 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op X1 X3) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq27 X2 X3 (M.op X1 X3)
       have i₂ := eq8 X3 X1 X0
       grind)
    | exact superpose eq8 eq27
    | exact resolve eq27 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op X2 X0) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 X1 X2 X2
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq27 X0 X1 X2
       have i₂ := eq12 X0 (M.op X1 X2)
       grind)
    | exact superpose eq12 eq27
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq27 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = (M.op X2 (M.op (M.op X3 X3) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq27 X2 (M.op X3 X3) X1
       have i₂ := eq8 X0 X1 X3
       grind)
    | exact superpose eq8 eq27
    | exact resolve eq27 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X1)) = (M.op (M.op X0 X0) (k X0 (M.op X0 X0))) := by
    intro X0 X1
    grind
  clear eq27
  have eq170 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X1)) = (k X2 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 X2 X1
       have i₂ := eq24 X2 X1 X0
       grind)
    | (have i₁ := eq60 X2 X1
       have i₂ := eq24 X0 X1 X2
       grind)
    | exact superpose eq24 eq60
    | exact resolve eq60 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = (k X2 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 X2 X1
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq60
    | exact resolve eq60 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 X1 : G, (k X1 (M.op X1 X1)) = (M.op (k X0 (M.op X0 X0)) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X1 x
       have i₂ := eq63 X0 x (M.op X1 X1)
       grind)
    | exact superpose eq63 eq60
    | exact resolve eq60 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq63
  have eq374 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq640 : ∀ X0 X2 X3 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X3 X3) (M.op X2 X2)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq8 x (M.op X2 X2) X3
       have i₂ := eq170 X2 x X0
       grind)
    | exact superpose eq170 eq8
    | exact resolve eq8 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq689 : ∀ X0 X1 X4 X5 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (M.op X4 (M.op X5 (M.op X4 X5))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq23 X5 X4 x x
       have i₂ := eq23 X1 X0 x x
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq1717 : ∀ X0 X1 X2 : G, (k X0 (M.op X0 X0)) ≠ (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (k X0 (M.op X0 X0)) = (k (M.op X2 X2) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq374 (M.op x x) (M.op X2 X2)
       have i₂ := eq640 X0 X2 x
       grind)
    | exact superpose eq640 eq374
    | exact resolve eq374 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1719 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) ≠ (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = (k (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq374 (M.op X0 X0) (M.op X1 X1)
       have i₂ := eq107 X0 X1
       grind)
    | exact superpose eq107 eq374
    | exact resolve eq374 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq1724 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq374 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq1728 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (k (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    grind
  clear eq1719
  have eq1730 : ∀ X0 X1 X2 : G, (k X0 (M.op X0 X0)) = (k (M.op X2 X2) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1717 X0 X1 X2
       grind)
    | (have r₁ := eq1717 X0 X2 X2
       have r₂ := eq640 X0 X2 X2
       grind)
    | exact resolve eq1717 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1717
  have eq1958 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq1724 (σ X0)
       grind)
    | exact superpose eq1724 eq13
    | exact resolve eq13 eq1724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1960 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46 X0 X0
       have i₂ := eq1724 (τ X0)
       grind)
    | exact superpose eq1724 eq46
    | exact resolve eq46 eq1724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq1967 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1960 X0
       have i₂ := eq1724 X0
       grind)
    | exact superpose eq1724 eq1960
    | exact resolve eq1960 eq1724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1960
  have eq1969 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1958 X0
       have i₂ := eq1724 X0
       grind)
    | exact superpose eq1724 eq1958
    | exact resolve eq1958 eq1724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1724 eq1958
  have eq2051 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (τ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 (τ X0)
       have i₂ := eq1967 X0
       grind)
    | exact superpose eq1967 eq8
    | exact resolve eq8 eq1967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2077 : ∀ X0 X1 X2 : G, (k X1 (M.op X1 X1)) = (M.op (M.op X2 X2) (τ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq640 X1 (τ X0) X2
       have i₂ := eq1967 X0
       grind)
    | exact superpose eq1967 eq640
    | exact resolve eq640 eq1967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640 eq1967
  have eq2244 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) (σ X0) X1
       have i₂ := eq1969 X0
       grind)
    | exact superpose eq1969 eq8
    | exact resolve eq8 eq1969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2256 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 (σ X0)
       have i₂ := eq1969 X0
       grind)
    | exact superpose eq1969 eq8
    | exact resolve eq8 eq1969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2264 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 X2 (σ X0)
       have i₂ := eq1969 X0
       grind)
    | exact superpose eq1969 eq24
    | exact resolve eq24 eq1969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2377 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq2455 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2377 X0 X1
       have i₂ := eq1969 X0
       grind)
    | exact superpose eq1969 eq2377
    | (have j0 := eq2377 X0 X1
       grind)
    | exact resolve eq2377 eq1969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2377
  have eq2527 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2455 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq2455
    | (have j0 := eq2455 X0 X1
       grind)
    | exact resolve eq2455 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2455
  have eq3679 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (σ (σ (M.op X0 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2256 (σ X0) X1 X2
       have i₂ := eq1969 X0
       grind)
    | exact superpose eq1969 eq2256
    | exact resolve eq2256 eq1969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1969
  have eq18990 : ∀ X0 X1 X2 : G, (k (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))) = (M.op (k X2 (M.op X2 X2)) (M.op X0 (M.op (M.op X1 X1) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq232 X0 (M.op X2 X2)
       have i₂ := eq8 X0 (M.op X2 X2) X2
       grind)
    | exact superpose eq8 eq232
    | exact resolve eq232 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq30294 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2527 x y
       grind)
    | exact superpose eq2527 eq14
    | (have j1 := eq2527 x y
       grind)
    | exact resolve eq14 eq2527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2527
  have eq30797 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq30294
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq30294
    | (have j1 := eq12 x y
       grind)
    | exact resolve eq30294 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30294
  have eq30803 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq30797
  have eq30804 : y = (M.op x x) := by grind
  clear eq30803
  have eq31492 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq8
    | exact resolve eq8 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31493 : (k x y) = (M.op y y) := by grind
  have eq31524 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) (M.op y X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq141 x X2 X0 X1
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq141
    | exact resolve eq141 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq31550 : ∀ X0 : G, (k x y) = (k (M.op X0 X0) y) := by
    intro X0
    first
    | (have i₁ := eq1728 x x
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq1728
    | exact resolve eq1728 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1728
  have eq31552 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (k y (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1730 X0 X1 x
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq1730
    | exact resolve eq1730 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31553 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (k (M.op X1 X1) y) := by
    intro X0 X1
    first
    | (have i₁ := eq1730 X0 x X1
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq1730
    | exact resolve eq1730 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31561 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X1 X1) (τ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq2077 x X0 X1
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq2077
    | exact resolve eq2077 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2077
  have eq31570 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq2244 x X0
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq2244
    | exact resolve eq2244 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2244
  have eq31571 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2256 x X0 X1
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq2256
    | exact resolve eq2256 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2256
  have eq31572 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2264 x X0 X1
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq2264
    | exact resolve eq2264 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2264
  have eq31597 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) X0)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq145 x x X0 X1
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq145
    | exact resolve eq145 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq31600 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq171 x x X0
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq171
    | exact resolve eq171 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31604 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq689 X0 X1 x x
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq689
    | exact resolve eq689 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq31621 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq31570 x
       have i₂ := eq31572 x (σ x)
       grind)
    | exact superpose eq31572 eq31570
    | exact resolve eq31570 eq31572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31570
  have eq31630 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (σ y) (τ y)) := by
    intro X0
    first
    | (have i₁ := eq31561 X0 x
       have i₂ := eq31572 x (τ y)
       grind)
    | exact superpose eq31572 eq31561
    | exact resolve eq31561 eq31572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31561
  have eq31638 : ∀ X1 : G, (k (M.op X1 X1) y) = (M.op x (M.op x y)) := by
    intro X1
    first
    | (have i₁ := eq31553 x X1
       have i₂ := eq31600 x
       grind)
    | exact superpose eq31600 eq31553
    | exact resolve eq31553 eq31600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31553
  have eq31639 : ∀ X1 : G, (k y (M.op X1 X1)) = (M.op x (M.op x y)) := by
    intro X1
    first
    | (have i₁ := eq31552 x X1
       have i₂ := eq31600 x
       grind)
    | exact superpose eq31600 eq31552
    | exact resolve eq31552 eq31600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31552
  have eq31661 : ∀ X1 X2 : G, (M.op (M.op X2 X1) (M.op y X2)) = (M.op (σ y) X1) := by
    intro X1 X2
    first
    | (have i₁ := eq31524 x X1 X2
       have i₂ := eq31571 x X1
       grind)
    | exact superpose eq31571 eq31524
    | exact resolve eq31524 eq31571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31524
  have eq31700 : (M.op x (M.op x y)) = (M.op (σ y) (τ y)) := by
    first
    | (have i₁ := eq31630 x
       have i₂ := eq31600 x
       grind)
    | exact superpose eq31600 eq31630
    | exact resolve eq31630 eq31600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31600 eq31630
  have eq31703 : (k x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq31638 x
       have i₂ := eq31550 x
       grind)
    | exact superpose eq31550 eq31638
    | exact resolve eq31638 eq31550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31550 eq31638
  have eq31743 : (M.op y y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq31703
       have i₂ := eq31493
       grind)
    | exact superpose eq31493 eq31703
    | exact resolve eq31703 eq31493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31493 eq31703
  have eq39575 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X3) X2)) = (M.op (M.op X3 X3) (k (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq146 X3 X2
       have i₂ := eq1730 X3 X1 X0
       grind)
    | (have i₁ := eq146 (M.op X2 X2) X1
       have i₂ := eq1730 X0 (M.op X2 X2) X2
       grind)
    | exact superpose eq1730 eq146
    | exact resolve eq146 eq1730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1730
  have eq39862 : ∀ X0 X1 X2 : G, (k X2 (M.op X2 X2)) = (M.op (M.op X1 X1) (M.op (k X1 (M.op X1 X1)) (M.op X0 (M.op (M.op X1 X1) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq171 (k X1 (M.op X1 X1)) (M.op X1 X1) X2
       have i₂ := eq146 X1 X0
       grind)
    | exact superpose eq146 eq171
    | exact resolve eq171 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq171
  have eq39887 : ∀ X0 X1 X2 : G, (k X2 (M.op X2 X2)) = (M.op (σ y) (M.op (k X1 (M.op X1 X1)) (M.op X0 (M.op (M.op X1 X1) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39862 X0 X1 X2
       have i₂ := eq31572 X1 (M.op (k X1 (M.op X1 X1)) (M.op X0 (M.op (M.op X1 X1) X0)))
       grind)
    | exact superpose eq31572 eq39862
    | exact resolve eq39862 eq31572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39862
  have eq40016 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X3) X2)) = (M.op (σ y) (k (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq39575 X0 X1 X2 X3
       have i₂ := eq31572 X3 (k (M.op X0 X0) (M.op X1 X1))
       grind)
    | exact superpose eq31572 eq39575
    | exact resolve eq39575 eq31572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31572 eq39575
  have eq40219 : ∀ X0 X1 X2 : G, (k X2 (M.op X2 X2)) = (M.op (σ y) (k (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39887 X0 X1 X2
       have i₂ := eq18990 X0 X1 X1
       grind)
    | exact superpose eq18990 eq39887
    | exact resolve eq39887 eq18990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18990 eq39887
  have eq40304 : ∀ X0 X1 : G, (M.op x (M.op x y)) = (M.op (σ y) (k (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq40016 X0 X1 x x
       have i₂ := eq31597 x x
       grind)
    | exact superpose eq31597 eq40016
    | exact resolve eq40016 eq31597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40016
  have eq40480 : ∀ X1 X2 : G, (k X2 (M.op X2 X2)) = (M.op (σ y) (k (M.op X1 X1) (M.op x (M.op x y)))) := by
    intro X1 X2
    first
    | (have i₁ := eq40219 x X1 X2
       have i₂ := eq31597 x X1
       grind)
    | exact superpose eq31597 eq40219
    | exact resolve eq40219 eq31597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31597 eq40219
  have eq40563 : ∀ X0 X1 : G, (M.op y y) = (M.op (σ y) (k (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq40304 X0 X1
       have i₂ := eq31743
       grind)
    | exact superpose eq31743 eq40304
    | exact resolve eq40304 eq31743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40304
  have eq40711 : ∀ X1 X2 : G, (k X2 (M.op X2 X2)) = (M.op (σ y) (k (M.op X1 X1) (M.op y y))) := by
    intro X1 X2
    first
    | (have i₁ := eq40480 X1 X2
       have i₂ := eq31743
       grind)
    | exact superpose eq31743 eq40480
    | exact resolve eq40480 eq31743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40480
  have eq40903 : ∀ X2 : G, (k X2 (M.op X2 X2)) = (M.op y y) := by
    intro X2
    first
    | (have i₁ := eq40711 x X2
       have i₂ := eq40563 x y
       grind)
    | exact superpose eq40563 eq40711
    | exact resolve eq40711 eq40563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40563 eq40711
  have eq44369 : ∀ X0 X1 : G, (k X1 X0) = (M.op y y) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq40903 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq40903 x
       have i₂ := eq12 X0 (M.op x x)
       grind)
    | exact superpose eq12 eq40903
    | (have j1 := eq12 y (k X1 X0)
       grind)
    | exact resolve eq40903 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40903
  have eq47176 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = (M.op y X2) ∨ (M.op X3 X2) = (k X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq31492 X1 X2
       have i₂ := eq41 X2 X0 X1 X3
       grind)
    | exact superpose eq41 eq31492
    | (have j1 := eq41 X2 X1 X2 X3
       grind)
    | exact resolve eq31492 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq47265 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq31492 x x
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq31492
    | exact resolve eq31492 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47391 : ∀ X0 X2 : G, (M.op (τ (M.op X2 X2)) X0) = (M.op y X0) := by
    intro X0 X2
    first
    | (have i₁ := eq2051 X2 x X0
       have i₂ := eq31492 x X0
       grind)
    | exact superpose eq31492 eq2051
    | exact resolve eq2051 eq31492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2051
  have eq47396 : ∀ X0 X2 : G, (M.op (σ (σ (M.op X2 X2))) X0) = (M.op y X0) := by
    intro X0 X2
    first
    | (have i₁ := eq3679 X2 x X0
       have i₂ := eq31492 x X0
       grind)
    | exact superpose eq31492 eq3679
    | exact resolve eq3679 eq31492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47459 : ∀ X0 X1 X2 : G, (M.op (σ (σ (M.op X2 X2))) X1) = (M.op (M.op X0 X1) (M.op y X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3679 X2 (M.op X0 X1) X1
       have i₂ := eq31492 X1 X0
       grind)
    | exact superpose eq31492 eq3679
    | exact resolve eq3679 eq31492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3679 eq31492
  have eq47628 : ∀ X1 X2 : G, (M.op (σ (σ (M.op X2 X2))) X1) = (M.op (σ y) X1) := by
    intro X1 X2
    first
    | (have i₁ := eq47459 x X1 X2
       have i₂ := eq31661 X1 x
       grind)
    | exact superpose eq31661 eq47459
    | exact resolve eq47459 eq31661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31661 eq47459
  have eq47875 : ∀ X2 X3 : G, (M.op y X2) = (M.op x (M.op x y)) ∨ (M.op X3 X2) = (k X3 X2) := by
    intro X2 X3
    first
    | (have i₁ := eq47176 x x X2 X3
       have i₂ := eq31604 x x
       grind)
    | exact superpose eq31604 eq47176
    | (have j0 := eq47176 x x X2 X3
       grind)
    | exact resolve eq47176 eq31604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31604 eq47176
  have eq47967 : ∀ X1 : G, (M.op y X1) = (M.op (σ y) X1) := by
    intro X1
    first
    | (have i₁ := eq47628 X1 x
       have i₂ := eq47396 X1 x
       grind)
    | exact superpose eq47396 eq47628
    | exact resolve eq47628 eq47396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47396 eq47628
  have eq48141 : ∀ X2 X3 : G, (M.op X3 X2) = (k X3 X2) ∨ (M.op y y) = (M.op y X2) := by
    intro X2 X3
    first
    | (have i₁ := eq47875 X2 X3
       have i₂ := eq31743
       grind)
    | exact superpose eq31743 eq47875
    | (have j0 := eq47875 X2 X3
       grind)
    | exact resolve eq47875 eq31743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47875
  have eq137862 : ∀ X0 : G, (M.op y X0) = (M.op (τ y) X0) := by
    intro X0
    first
    | (have i₁ := eq47391 X0 x
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq47391
    | exact resolve eq47391 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30804 eq47391
  have eq139744 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op (τ y) X1)) ∨ (M.op y X0) = (k (τ y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq142 X0 X1 (τ y)
       have i₂ := eq137862 X0
       grind)
    | exact superpose eq137862 eq142
    | exact resolve eq142 eq137862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq139963 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) (τ y)) ∨ (M.op y X0) = (k (τ y) X0) := by
    intro X0
    first
    | (have i₁ := eq139744 X0 x
       have i₂ := eq31571 x (τ y)
       grind)
    | exact superpose eq31571 eq139744
    | (have j0 := eq139744 X0 x
       grind)
    | exact resolve eq139744 eq31571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31571 eq139744
  have eq140259 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op x y)) ∨ (M.op y X0) = (k (τ y) X0) := by
    intro X0
    first
    | (have i₁ := eq139963 X0
       have i₂ := eq31700
       grind)
    | exact superpose eq31700 eq139963
    | (have j0 := eq139963 X0
       grind)
    | exact resolve eq139963 eq31700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31700 eq139963
  have eq140463 : ∀ X0 : G, (M.op y y) = (M.op y X0) ∨ (M.op y X0) = (k (τ y) X0) := by
    intro X0
    first
    | (have i₁ := eq140259 X0
       have i₂ := eq31743
       grind)
    | exact superpose eq31743 eq140259
    | (have j0 := eq140259 X0
       grind)
    | exact resolve eq140259 eq31743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140259
  have eq166743 : ∀ X0 X1 : G, (k y X0) = (M.op x (M.op x y)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31639 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq31639 X1
       have i₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact superpose eq12 eq31639
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq31639 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31639
  have eq166960 : ∀ X0 X1 : G, (M.op y y) = (k y X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq166743 X0 X1
       have i₂ := eq31743
       grind)
    | exact superpose eq31743 eq166743
    | (have j0 := eq166743 X0 X1
       grind)
    | exact resolve eq166743 eq31743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31743 eq166743
  have eq207742 : (M.op (σ x) (σ y)) = (M.op y (σ x)) := by
    first
    | (have i₁ := eq47967 (σ x)
       have i₂ := eq31621
       grind)
    | exact superpose eq31621 eq47967
    | exact resolve eq47967 eq31621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31621 eq47967
  have eq210776 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq207742
       grind)
    | exact superpose eq207742 eq14
    | exact resolve eq14 eq207742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207742
  have eq1159253 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op y y) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44369 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44369
  have eq1229210 : ∀ X0 : G, (M.op y y) ≠ (M.op y X0) ∨ (M.op y X0) = (k (τ y) X0) := by
    intro X0
    first
    | (have i₁ := eq1159253 (τ y) X0
       have i₂ := eq137862 X0
       grind)
    | exact superpose eq137862 eq1159253
    | (have j0 := eq1159253 y X0
       grind)
    | (have r₁ := eq1159253 (τ y) y
       have r₂ := eq137862 y
       grind)
    | exact resolve eq1159253 eq137862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137862 eq1159253
  have eq1229217 : ∀ X0 : G, (M.op y X0) = (k (τ y) X0) := by
    intro X0
    first
    | (have j0 := eq1229210 X0
       have j1 := eq140463 X0
       grind)
    | (have r₁ := eq1229210 X0
       have r₂ := eq140463 X0
       grind)
    | (have r₁ := eq1229210 y
       have r₂ := eq140463 y
       grind)
    | exact resolve eq1229210 eq140463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140463 eq1229210
  have eq1229258 : ∀ X0 : G, (σ (M.op y X0)) = (k y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16 y X0
       have i₂ := eq1229217 X0
       grind)
    | exact superpose eq1229217 eq16
    | exact resolve eq16 eq1229217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq1229217
  have eq1374660 : ∀ X0 : G, (M.op y y) ≠ (M.op y X0) ∨ (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq166960 X0 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166960
  have eq1374662 : ∀ X0 : G, (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq1374660 X0
       have j1 := eq48141 X0 y
       grind)
    | (have r₁ := eq1374660 x
       have r₂ := eq48141 x x
       grind)
    | (have r₁ := eq1374660 y
       have r₂ := eq48141 y x
       grind)
    | exact resolve eq1374660 eq48141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48141 eq1374660
  have eq1374723 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq1229258 X0
       have i₂ := eq1374662 (σ X0)
       grind)
    | exact superpose eq1374662 eq1229258
    | exact resolve eq1229258 eq1374662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229258 eq1374662
  have eq1382749 : (σ (M.op x y)) = (M.op y (σ x)) := by
    first
    | (have i₁ := eq1374723 x
       have i₂ := eq47265
       grind)
    | exact superpose eq47265 eq1374723
    | exact resolve eq1374723 eq47265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47265 eq1374723
  have eq1382928 : False := by grind
  exact eq1382928

/-- `Equation4478`: `x ◇ (y ◇ y) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pyx_pxx_pyx_Equation4478 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4478 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4478.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq492 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq496 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq492 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq492 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq492 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq492 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq531 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq496 (σ X1) (σ X0)
       grind)
    | exact superpose eq496 eq13
    | exact resolve eq13 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq531 X0 X1
       have i₂ := eq496 X1 X0
       grind)
    | exact superpose eq496 eq531
    | exact resolve eq531 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496 eq531
  have eq1747 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq542 x y
       grind)
    | exact superpose eq542 eq14
    | (have r₁ := eq14
       have r₂ := eq542 x y
       grind)
    | exact resolve eq14 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq1778 : False := by grind
  exact eq1778

/-- `Equation4485`: `x ◇ (y ◇ y) = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pxy_Equation4485 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4485 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X0 X3
       have i₂ := eq8 X2 X0 X1
       grind)
    | (have i₁ := eq8 (M.op X1 X2) X1 X2
       have i₂ := eq8 (M.op X1 X1) X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X2 (M.op X0 X0)
       have i₂ := eq8 X2 X0 X1
       grind)
    | (have i₁ := eq8 X0 (M.op X1 X2) X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X1) = (M.op X1 X0) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X0 X2
       have i₂ := eq12 X3 X0
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
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
  have eq36 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq39 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
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
  have eq40 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq34 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq47 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq60 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X4) = (M.op (M.op X2 X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq19 X2 X3 X4 (M.op X0 X0)
       have i₂ := eq8 X2 X0 X1
       grind)
    | (have i₁ := eq19 (M.op X1 X2) X1 X2 X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = (M.op (M.op X2 X4) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op X0 X3) X2 X4
       have i₂ := eq19 X0 X3 (M.op X2 X2) X1
       grind)
    | (have i₁ := eq8 (M.op X0 X3) X2 X4
       have i₂ := eq19 X0 X1 (M.op X2 X2) X3
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq101 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq40 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq40 eq13
    | (have j1 := eq40 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X2 (τ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq40 (τ X1) X2 X0
       grind)
    | exact superpose eq40 eq16
    | (have j1 := eq40 (τ X1) X2 X2
       grind)
    | exact resolve eq16 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq40 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47 X0 X1
       have i₂ := eq40 X1 (σ X0) X2
       grind)
    | exact superpose eq40 eq47
    | (have j1 := eq40 X1 X1 X2
       grind)
    | exact resolve eq47 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq121 : ∀ X0 X1 X2 : G, (k X0 (τ X1)) = X0 ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq112 X0 X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq112
    | (have j0 := eq112 X0 X1 X2
       grind)
    | exact resolve eq112 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq127 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X0 X1) (M.op X0 X2))) = (M.op (M.op (M.op X4 X5) (M.op X0 X2)) X3) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq21 X4 X5 (M.op X0 X2) X3
       have i₂ := eq19 X0 X2 (M.op X0 X2) X1
       grind)
    | (have i₁ := eq21 X4 X5 (M.op X0 X2) X3
       have i₂ := eq19 X0 X1 (M.op X0 X2) X2
       grind)
    | exact superpose eq19 eq21
    | exact resolve eq21 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (M.op X2 X3) X4) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq19 (M.op X2 X3) X1 X0 X4
       have i₂ := eq21 X2 X3 X1 X0
       grind)
    | (have i₁ := eq19 X0 X1 (M.op X2 X2) X3
       have i₂ := eq21 X0 X1 X2 (M.op X0 X1)
       grind)
    | exact superpose eq21 eq19
    | exact resolve eq19 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq21
  have eq182 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X1 X2) ∨ (M.op X1 X2) = (k (M.op X1 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq105 (M.op X1 X2) X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | (have i₁ := eq105 X0 (M.op X1 X1)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq105
    | (have j0 := eq105 (M.op X1 X2) X0
       grind)
    | (have r₁ := eq105 (M.op X0 (M.op X0 X0)) X0
       have r₂ := eq8 X0 X0 (M.op X0 X0)
       grind)
    | exact resolve eq105 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq485 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 X1) ∨ (k X3 X1) = (M.op X3 X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq33 X1 X0 x X3
       grind)
    | exact superpose eq33 eq8
    | (have j1 := eq33 X1 X1 x X3
       grind)
    | exact resolve eq8 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq845 : ∀ X0 X1 X4 X5 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X4 X5) X0) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq60 x x X4 X5 X0
       have i₂ := eq168 X0 X1 x x X4
       grind)
    | (have i₁ := eq60 X0 X1 x x (M.op X1 X1)
       have i₂ := eq168 (M.op (M.op X0 X1) x) X1 x x X4
       grind)
    | exact superpose eq168 eq60
    | exact resolve eq60 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq168
  have eq1162 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X4) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X2 X3 X4
       have i₂ := eq845 X2 X3 X0 X1
       grind)
    | (have i₁ := eq8 (M.op X4 x) X1 X2
       have i₂ := eq845 (M.op X1 X1) X1 X4 x
       grind)
    | exact superpose eq845 eq8
    | exact resolve eq8 eq845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2119 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 (σ X0)) = (M.op X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq121 X1 (σ X0) X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq121
    | (have j0 := eq121 X0 (σ X0) X2
       grind)
    | exact resolve eq121 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq2174 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ X0)
       have i₂ := eq38 X0 X0
       grind)
    | exact superpose eq38 eq11
    | (have j0 := eq11 X1 (σ X0)
       have j1 := eq38 X0 X0
       grind)
    | (have r₁ := eq11 X0 (σ X1)
       have r₂ := eq38 X0 X1
       grind)
    | exact resolve eq11 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2242 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq38 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq2246 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2174 X0 X1
       have j1 := eq11 X1 (σ X0)
       grind)
    | (have r₁ := eq2174 X0 X1
       have r₂ := eq11 X0 (σ X0)
       grind)
    | exact resolve eq2174 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2174
  have eq2263 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2246 (τ X0) X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq2246
    | (have j0 := eq2246 (τ X0) X1
       grind)
    | exact resolve eq2246 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2267 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2263 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2263
    | (have j0 := eq2263 X0 X1
       grind)
    | exact resolve eq2263 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2263
  have eq2271 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2267 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2267
    | (have j0 := eq2267 X0 X1
       grind)
    | exact resolve eq2267 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2267
  have eq2480 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2271 (τ X0) X1
       have i₂ := eq82 X0 X0
       grind)
    | exact superpose eq82 eq2271
    | (have j0 := eq2271 (τ X0) X1
       grind)
    | exact resolve eq2271 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq2271
  have eq3192 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq39 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq39
    | (have j0 := eq39 X0 X1
       grind)
    | exact resolve eq39 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq3341 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3192 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq3192
    | (have j0 := eq3192 X0 X1
       grind)
    | exact resolve eq3192 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3192
  have eq4216 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0 X0
       have i₂ := eq3341 X1 X0
       grind)
    | exact superpose eq3341 eq105
    | (have j0 := eq105 X0 X0
       have j1 := eq3341 X1 X0
       grind)
    | (have r₁ := eq105 X1 X1
       have r₂ := eq3341 X0 X1
       grind)
    | exact resolve eq105 eq3341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq4261 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4216 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4216
  have eq7234 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2246 X0 X1
       have i₂ := eq4261 X0 X2
       grind)
    | exact superpose eq4261 eq2246
    | (have j0 := eq2246 X0 X1
       have j1 := eq4261 X0 X2
       grind)
    | exact resolve eq2246 eq4261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2246 eq4261
  have eq7284 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq7234 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7234
  have eq8595 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2242 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq2242
    | (have j0 := eq2242 (τ X0)
       grind)
    | exact resolve eq2242 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8611 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq8595 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8595
    | (have j0 := eq8595 X0
       grind)
    | exact resolve eq8595 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8595
  have eq8618 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8611 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8611
    | (have j0 := eq8611 X0
       grind)
    | exact resolve eq8611 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8611
  have eq9341 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq101 x y X0
       grind)
    | exact superpose eq101 eq14
    | (have j1 := eq101 X0 y X0
       grind)
    | exact resolve eq14 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq9462 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq9341 X0
       have j1 := eq7284 y X0 x
       grind)
    | (have r₁ := eq9341 X0
       have r₂ := eq7284 y x x
       grind)
    | exact resolve eq9341 eq7284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7284 eq9341
  have eq9497 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq8618 (σ y)
       have i₂ := eq9462 (σ y)
       grind)
    | exact superpose eq9462 eq8618
    | (have j0 := eq8618 (σ y)
       grind)
    | (have r₁ := eq8618 (σ y)
       have r₂ := eq9462 (σ y)
       grind)
    | exact resolve eq8618 eq9462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9499 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k X0 (τ (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2480 (σ y) X0
       have i₂ := eq9462 (σ y)
       grind)
    | exact superpose eq9462 eq2480
    | (have j0 := eq2480 (σ y) X0
       grind)
    | exact resolve eq2480 eq9462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9462
  have eq9525 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq9499 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9499
  have eq9527 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq9497
  have eq9535 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq9525 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq9525
    | exact resolve eq9525 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9525
  have eq9700 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq8618 y
       have i₂ := eq9535 y
       grind)
    | exact superpose eq9535 eq8618
    | (have j0 := eq8618 y
       grind)
    | (have r₁ := eq8618 y
       have r₂ := eq9535 y
       grind)
    | exact resolve eq8618 eq9535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9707 : ∀ X0 X1 : G, (M.op X0 y) = X0 ∨ (M.op y X1) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq36 y X1 X0
       have i₂ := eq9535 X0
       grind)
    | exact superpose eq9535 eq36
    | (have j0 := eq36 y X1 x
       grind)
    | exact resolve eq36 eq9535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq9535
  have eq9727 : y = (M.op y y) := by grind
  clear eq9700
  have eq10045 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (M.op X0 y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq845 X0 y X1 X2
       have i₂ := eq9727
       grind)
    | exact superpose eq9727 eq845
    | exact resolve eq845 eq9727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10050 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq8 X0 y y
       have i₂ := eq9727
       grind)
    | exact superpose eq9727 eq8
    | exact resolve eq8 eq9727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10071 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) y) = (M.op y (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80 X0 X1 y x y
       have i₂ := eq9727
       grind)
    | exact superpose eq9727 eq80
    | exact resolve eq80 eq9727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq10087 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y X0) := by
    intro X0 X1
    first
    | (have i₁ := eq845 X0 X1 y y
       have i₂ := eq9727
       grind)
    | exact superpose eq9727 eq845
    | exact resolve eq845 eq9727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq10089 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1162 X0 X1 X2 y y
       have i₂ := eq9727
       grind)
    | exact superpose eq9727 eq1162
    | exact resolve eq1162 eq9727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10100 : ∀ X0 X2 : G, (M.op y y) = (M.op y (M.op X0 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq10071 X0 x X2
       have i₂ := eq10089 X0 x y
       grind)
    | exact superpose eq10089 eq10071
    | exact resolve eq10071 eq10089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10071
  have eq10119 : ∀ X0 X2 : G, y = (M.op y (M.op X0 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq10100 X0 X2
       have i₂ := eq9727
       grind)
    | exact superpose eq9727 eq10100
    | exact resolve eq10100 eq9727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9727 eq10100
  have eq19794 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (σ y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1162 X0 X1 X2 (σ y) (σ y)
       have i₂ := eq9527
       grind)
    | exact superpose eq9527 eq1162
    | exact resolve eq1162 eq9527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162
  have eq19796 : y = (M.op y (σ y)) := by
    first
    | (have i₁ := eq10119 (σ y) (σ y)
       have i₂ := eq9527
       grind)
    | exact superpose eq9527 eq10119
    | exact resolve eq10119 eq9527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19801 : ∀ X2 : G, (M.op (σ y) X2) = (M.op y X2) := by
    intro X2
    first
    | (have i₁ := eq19794 x x X2
       have i₂ := eq10089 x x X2
       grind)
    | exact superpose eq10089 eq19794
    | exact resolve eq19794 eq10089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19794
  have eq22032 : (σ y) = (M.op y (σ y)) := by
    first
    | (have i₁ := eq9527
       have i₂ := eq19801 (σ y)
       grind)
    | exact superpose eq19801 eq9527
    | exact resolve eq9527 eq19801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9527 eq19801
  have eq22202 : y = (σ y) := by
    first
    | (have i₁ := eq22032
       have i₂ := eq19796
       grind)
    | exact superpose eq19796 eq22032
    | exact resolve eq22032 eq19796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19796 eq22032
  have eq23116 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq22202
       grind)
    | exact superpose eq22202 eq14
    | exact resolve eq14 eq22202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23123 : ∀ X0 : G, (k y (σ X0)) = (σ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq22202
       grind)
    | exact superpose eq22202 eq13
    | exact resolve eq13 eq22202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23137 : ∀ X0 : G, (k y (τ X0)) = (τ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq47 y X0
       have i₂ := eq22202
       grind)
    | exact superpose eq22202 eq47
    | exact resolve eq47 eq22202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq23152 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq23116
       have i₂ := eq10050 (σ x)
       grind)
    | exact superpose eq10050 eq23116
    | exact resolve eq23116 eq10050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23116
  have eq30888 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (σ (M.op (τ X0) (M.op (M.op X1 X2) (M.op X1 X3)))) = (k (σ (M.op (M.op X4 X5) (M.op X1 X3))) X0) ∨ (k X6 (τ X0)) = X6 := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq103 (M.op (M.op X4 X5) (M.op X1 X3)) X0 X6
       have i₂ := eq127 X1 X2 X3 (τ X0) X4 X5
       grind)
    | exact superpose eq127 eq103
    | (have j0 := eq103 X0 X0 X6
       grind)
    | exact resolve eq103 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq127
  have eq30891 : ∀ X0 X1 X2 X3 X6 : G, (σ (M.op (τ X0) (M.op (M.op X1 X2) (M.op X1 X3)))) = (k (σ (M.op y (M.op X1 X3))) X0) ∨ (k X6 (τ X0)) = X6 := by
    intro X0 X1 X2 X3 X6
    first
    | (have i₁ := eq30888 X0 X1 X2 X3 x x X6
       have i₂ := eq10089 x x (M.op X1 X3)
       grind)
    | exact superpose eq10089 eq30888
    | (have j0 := eq30888 X0 X1 X2 X3 x x X6
       grind)
    | exact resolve eq30888 eq10089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30888
  have eq31059 : ∀ X0 X1 X2 X3 X6 : G, (σ (M.op (τ X0) (M.op (M.op X1 X2) (M.op X1 X3)))) = (k (σ y) X0) ∨ (k X6 (τ X0)) = X6 := by
    intro X0 X1 X2 X3 X6
    first
    | (have i₁ := eq30891 X0 X1 X2 X3 X6
       have i₂ := eq10119 X1 X3
       grind)
    | exact superpose eq10119 eq30891
    | (have j0 := eq30891 X0 X1 X2 X3 X6
       grind)
    | exact resolve eq30891 eq10119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30891
  have eq31218 : ∀ X0 X1 X2 X3 X6 : G, (σ (M.op (τ X0) (M.op (M.op X1 X2) (M.op X1 X3)))) = (k y X0) ∨ (k X6 (τ X0)) = X6 := by
    intro X0 X1 X2 X3 X6
    first
    | (have i₁ := eq31059 X0 X1 X2 X3 X6
       have i₂ := eq22202
       grind)
    | exact superpose eq22202 eq31059
    | (have j0 := eq31059 X0 X1 X2 X3 X6
       grind)
    | exact resolve eq31059 eq22202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31059
  have eq31332 : ∀ X0 X1 X3 X6 : G, (σ (M.op (τ X0) (M.op y (M.op X1 X3)))) = (k y X0) ∨ (k X6 (τ X0)) = X6 := by
    intro X0 X1 X3 X6
    first
    | (have i₁ := eq31218 X0 X1 x X3 X6
       have i₂ := eq10089 X1 x (M.op X1 X3)
       grind)
    | exact superpose eq10089 eq31218
    | (have j0 := eq31218 X0 X1 x X3 X6
       grind)
    | exact resolve eq31218 eq10089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31218
  have eq31341 : ∀ X0 X6 : G, (σ (M.op (τ X0) y)) = (k y X0) ∨ (k X6 (τ X0)) = X6 := by
    intro X0 X6
    first
    | (have i₁ := eq31332 X0 x x X6
       have i₂ := eq10119 x x
       grind)
    | exact superpose eq10119 eq31332
    | (have j0 := eq31332 X0 x x X6
       grind)
    | exact resolve eq31332 eq10119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31332
  have eq31349 : ∀ X0 X6 : G, (σ (M.op y (τ X0))) = (k y X0) ∨ (k X6 (τ X0)) = X6 := by
    intro X0 X6
    first
    | (have i₁ := eq31341 X0 X6
       have i₂ := eq10050 (τ X0)
       grind)
    | exact superpose eq10050 eq31341
    | (have j0 := eq31341 X0 X6
       grind)
    | exact resolve eq31341 eq10050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31341
  have eq38564 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op y X0) ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq485 X0 X1 X2
       have i₂ := eq10087 X0 X1
       grind)
    | exact superpose eq10087 eq485
    | (have j0 := eq485 X0 X1 X2
       grind)
    | exact resolve eq485 eq10087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41672 : ∀ X0 X1 : G, (M.op y (σ X0)) = (σ (k y X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2119 X0 X1 y
       have i₂ := eq23123 X0
       grind)
    | exact superpose eq23123 eq2119
    | (have j0 := eq2119 X0 X1 x
       grind)
    | exact resolve eq2119 eq23123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2119
  have eq99839 : ∀ X0 : G, (M.op y X0) ≠ X0 ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq9707 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9707
  have eq103998 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op y X0) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) y) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq99839 (M.op X0 X0)
       have i₂ := eq485 y X0 X1
       grind)
    | exact superpose eq485 eq99839
    | (have j0 := eq99839 (M.op X0 X0)
       have j1 := eq485 X0 X0 X1
       grind)
    | (have r₁ := eq99839 (M.op y y)
       have r₂ := eq485 y y x
       grind)
    | exact resolve eq99839 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485 eq99839
  have eq104059 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) y) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq103998 X0 X1
       have j1 := eq38564 X0 X0 X1
       grind)
    | (have r₁ := eq103998 X1 X1
       have r₂ := eq38564 X1 X1 x
       grind)
    | (have r₁ := eq103998 y X1
       have r₂ := eq38564 y y x
       grind)
    | exact resolve eq103998 eq38564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38564 eq103998
  have eq104106 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op y (M.op X0 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq104059 X0 X1
       have i₂ := eq8 y X0 X0
       grind)
    | exact superpose eq8 eq104059
    | (have j0 := eq104059 X0 X1
       grind)
    | exact resolve eq104059 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104059
  have eq104153 : ∀ X0 X1 : G, y = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq104106 X0 X1
       have i₂ := eq10119 X0 X0
       grind)
    | exact superpose eq10119 eq104106
    | (have j0 := eq104106 X0 X1
       grind)
    | exact resolve eq104106 eq10119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10119 eq104106
  have eq121300 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op y X0)) ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq23137 X0
       have i₂ := eq104153 X0 y
       grind)
    | exact superpose eq104153 eq23137
    | (have j1 := eq104153 X0 x
       grind)
    | exact resolve eq23137 eq104153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23137 eq104153
  have eq535751 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k y X1) = (σ (M.op y (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 (τ X1)
       have i₂ := eq31349 X1 (τ X0)
       grind)
    | exact superpose eq31349 eq15
    | (have j1 := eq31349 X1 x
       grind)
    | exact resolve eq15 eq31349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq31349
  have eq535752 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k y X1) = (σ (M.op y (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq535751 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq535751
    | (have j0 := eq535751 X0 X1
       grind)
    | exact resolve eq535751 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535751
  have eq535761 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k y X1) = (σ (M.op y (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq535752 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq535752
    | (have j0 := eq535752 X0 X1
       grind)
    | exact resolve eq535752 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535752
  have eq541829 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (σ (M.op y (τ X0))) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq8618 X0
       have i₂ := eq535761 X0 X0
       grind)
    | exact superpose eq535761 eq8618
    | (have j0 := eq8618 X0
       have j1 := eq535761 X0 X0
       grind)
    | (have r₁ := eq8618 x
       have r₂ := eq535761 x x
       grind)
    | exact resolve eq8618 eq535761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535761
  have eq541871 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op y (τ X0))) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq541829 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541829
  have eq561204 : ∀ X0 X1 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3341 y X0
       have i₂ := eq41672 X0 X1
       grind)
    | exact superpose eq41672 eq3341
    | (have j0 := eq3341 X0 X0
       have j1 := eq41672 X0 X1
       grind)
    | exact resolve eq3341 eq41672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3341 eq41672
  have eq561262 : ∀ X0 X1 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq561204 X0 X1
       have j1 := eq11 X1 X0
       grind)
    | (have r₁ := eq561204 X1 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq561204 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561204
  have eq563551 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have j0 := eq182 X0 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq563552 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) X0) := by
    intro X0
    first
    | (have i₁ := eq563551 x
       have i₂ := eq10087 x x
       grind)
    | exact superpose eq10087 eq563551
    | exact resolve eq563551 eq10087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10087 eq563551
  have eq563832 : ∀ X0 : G, (σ (M.op y (τ X0))) = (k (σ (M.op y (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op y (τ X0))
       have i₂ := eq563552 (τ X0)
       grind)
    | exact superpose eq563552 eq16
    | exact resolve eq16 eq563552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563552
  have eq564652 : ∀ X0 : G, (k y X0) = (k (k y X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq563832 X0
       have i₂ := eq541871 X0
       grind)
    | exact superpose eq541871 eq563832
    | (have j1 := eq541871 X0
       grind)
    | exact resolve eq563832 eq541871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541871 eq563832
  have eq564801 : ∀ X0 : G, (k y X0) = (k (k y X0) X0) := by
    intro X0
    first
    | (have j0 := eq564652 X0
       have j1 := eq11 (k y X0) X0
       grind)
    | (have r₁ := eq564652 x
       have r₂ := eq11 X0 x
       grind)
    | exact resolve eq564652 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564652
  have eq564990 : ∀ X0 : G, (k y X0) = (M.op (k y X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 (k y X0) X0
       have i₂ := eq564801 X0
       grind)
    | exact superpose eq564801 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq564801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564801
  have eq565271 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (k y X0) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10045 X1 (k y X0) X0
       have i₂ := eq564990 X0
       grind)
    | exact superpose eq564990 eq10045
    | (have j1 := eq564990 X0
       grind)
    | exact resolve eq10045 eq564990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10045
  have eq567484 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq564990 X0
       have i₂ := eq565271 X0 X0
       grind)
    | exact superpose eq565271 eq564990
    | (have j0 := eq564990 X0
       have j1 := eq565271 X0 x
       grind)
    | exact resolve eq564990 eq565271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564990 eq565271
  have eq567578 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq567484 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567484
  have eq573957 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op X0 y)) ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq121300 X0
       have i₂ := eq10050 X0
       grind)
    | (have i₁ := eq121300 y
       have i₂ := eq10050 y
       grind)
    | exact superpose eq10050 eq121300
    | (have j0 := eq121300 X0
       grind)
    | exact resolve eq121300 eq10050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121300
  have eq578633 : ∀ X0 X1 : G, (σ (M.op X0 y)) = (M.op y (σ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq561262 X0 X1
       have i₂ := eq10050 X0
       grind)
    | (have i₁ := eq561262 y X1
       have i₂ := eq10050 y
       grind)
    | exact superpose eq10050 eq561262
    | (have j0 := eq561262 X0 X1
       grind)
    | exact resolve eq561262 eq10050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561262
  have eq646029 : ∀ X0 : G, (M.op X0 y) = (σ (k y (τ X0))) ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 y)
       have i₂ := eq573957 X0
       grind)
    | exact superpose eq573957 eq10
    | (have j1 := eq573957 X0
       grind)
    | exact resolve eq10 eq573957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573957
  have eq646069 : ∀ X0 : G, (M.op X0 y) = (k (σ y) X0) ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq646029 X0
       have i₂ := eq16 X0 y
       grind)
    | exact superpose eq16 eq646029
    | (have j0 := eq646029 X0
       grind)
    | exact resolve eq646029 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq646029
  have eq646084 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq646069 X0
       have i₂ := eq22202
       grind)
    | exact superpose eq22202 eq646069
    | (have j0 := eq646069 X0
       grind)
    | exact resolve eq646069 eq22202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646069
  have eq646275 : ∀ X0 : G, y = X0 ∨ (M.op X0 y) = (k y X0) ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq567578 X0
       have i₂ := eq646084 X0
       grind)
    | exact superpose eq646084 eq567578
    | (have j0 := eq567578 X0
       have j1 := eq646084 X0
       grind)
    | exact resolve eq567578 eq646084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567578 eq646084
  have eq646325 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq646275 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646275
  have eq647844 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) y) ∨ (σ X0) = y := by
    intro X0
    first
    | (have i₁ := eq23123 X0
       have i₂ := eq646325 (σ X0)
       grind)
    | exact superpose eq646325 eq23123
    | (have j1 := eq646325 (σ X0)
       grind)
    | exact resolve eq23123 eq646325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23123 eq646325
  have eq648143 : ∀ X0 : G, (M.op y (σ X0)) = (σ (k y X0)) ∨ (σ X0) = y := by
    intro X0
    first
    | (have i₁ := eq647844 X0
       have i₂ := eq10050 (σ X0)
       grind)
    | exact superpose eq10050 eq647844
    | (have j0 := eq647844 X0
       grind)
    | exact resolve eq647844 eq10050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10050 eq647844
  have eq701601 : ∀ X0 : G, (M.op y (σ x)) ≠ (M.op y (σ x)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq23152
       have i₂ := eq578633 x X0
       grind)
    | exact superpose eq578633 eq23152
    | (have j1 := eq578633 x X0
       grind)
    | (have r₁ := eq23152
       have r₂ := eq578633 x x
       grind)
    | exact resolve eq23152 eq578633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23152 eq578633
  have eq701615 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq701601 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701601
  have eq707298 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2242 x
       have i₂ := eq701615 x
       grind)
    | exact superpose eq701615 eq2242
    | (have j0 := eq2242 x
       grind)
    | exact resolve eq2242 eq701615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2242
  have eq707302 : ∀ X0 : G, (τ x) ≠ (τ x) ∨ (k X0 (τ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2480 x X0
       have i₂ := eq701615 x
       grind)
    | exact superpose eq701615 eq2480
    | (have j0 := eq2480 x X0
       grind)
    | exact resolve eq2480 eq701615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2480
  have eq707303 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq8618 x
       have i₂ := eq701615 x
       grind)
    | exact superpose eq701615 eq8618
    | (have j0 := eq8618 x
       grind)
    | (have r₁ := eq8618 x
       have r₂ := eq701615 x
       grind)
    | exact resolve eq8618 eq701615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8618 eq701615
  have eq707608 : x = (M.op x x) := by grind
  clear eq707303
  have eq707609 : ∀ X0 : G, (k X0 (τ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq707302 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707302
  have eq707613 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq707298
  have eq708628 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq10089 x x X0
       have i₂ := eq707608
       grind)
    | exact superpose eq707608 eq10089
    | exact resolve eq10089 eq707608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10089
  have eq709623 : (σ y) = (M.op y (σ (τ x))) ∨ y = (σ (τ x)) := by
    first
    | (have i₁ := eq648143 (τ x)
       have i₂ := eq707609 y
       grind)
    | exact superpose eq707609 eq648143
    | (have j0 := eq648143 (τ x)
       grind)
    | exact resolve eq648143 eq707609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648143 eq707609
  have eq709636 : (σ y) = (M.op x (σ (τ x))) ∨ y = (σ (τ x)) := by
    first
    | (have i₁ := eq709623
       have i₂ := eq708628 (σ (τ x))
       grind)
    | exact superpose eq708628 eq709623
    | exact resolve eq709623 eq708628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708628 eq709623
  have eq709812 : (σ y) = (M.op x x) ∨ y = (σ (τ x)) := by
    first
    | (have i₁ := eq709636
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq709636
    | exact resolve eq709636 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709636
  have eq709877 : x = (σ y) ∨ y = (σ (τ x)) := by
    first
    | (have i₁ := eq709812
       have i₂ := eq707608
       grind)
    | exact superpose eq707608 eq709812
    | exact resolve eq709812 eq707608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709812
  have eq709901 : x = y ∨ y = (σ (τ x)) := by
    first
    | (have i₁ := eq709877
       have i₂ := eq22202
       grind)
    | exact superpose eq22202 eq709877
    | exact resolve eq709877 eq22202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22202 eq709877
  have eq709909 : x = y ∨ x = y := by
    first
    | (have i₁ := eq709901
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq709901
    | exact resolve eq709901 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709901
  have eq709910 : x = y := by grind
  clear eq709909
  have eq709913 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq709910
       grind)
    | exact superpose eq709910 eq14
    | exact resolve eq14 eq709910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709910
  have eq710329 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq709913
       have i₂ := eq707608
       grind)
    | exact superpose eq707608 eq709913
    | exact resolve eq709913 eq707608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707608 eq709913
  have eq710336 : False := by grind
  exact eq710336

/-- `Equation4497`: `x ◇ (y ◇ y) = (z ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pxy_Equation4497 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4497 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4497.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X2) X0) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op X2 (M.op (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X1 X1) X3
       have i₂ := eq8 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq8 X2 (M.op X0 X0) X3
       have i₂ := eq8 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 x X3
       have i₂ := eq8 X1 x X0
       grind)
    | (have i₁ := eq8 (M.op x x) X1 x
       have i₂ := eq8 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X0 X2 x
       grind)
    | (have i₁ := eq8 (M.op X1 X1) X1 X2
       have i₂ := eq8 (M.op X2 X2) X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op X2 X2) (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X0 X0) X1 X3
       have i₂ := eq8 (M.op X3 X3) X0 X2
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X1) = (M.op X1 X0) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X0 X2
       have i₂ := eq12 X3 X0
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq40 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
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
  have eq41 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq36 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq48 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq83 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30
    | exact resolve eq30 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq159 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq41 X1 (σ X0) X2
       grind)
    | exact superpose eq41 eq48
    | (have j1 := eq41 X1 X1 X2
       grind)
    | exact resolve eq48 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq41 X1 (τ X0) X2
       grind)
    | exact superpose eq41 eq15
    | (have j1 := eq41 X1 X1 X2
       grind)
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq164 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq41 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq41 eq13
    | (have j1 := eq41 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq41 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq170 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = X0 ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq160 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq160
    | (have j0 := eq160 X0 X1 X2
       grind)
    | exact resolve eq160 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq171 : ∀ X0 X1 X2 : G, (k X0 (τ X1)) = X0 ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq159 X0 X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq159
    | (have j0 := eq159 X0 X1 X2
       grind)
    | exact resolve eq159 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq174 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) ≠ X1 ∨ (k X1 (M.op X2 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq169 X1 (M.op X2 X2)
       have i₂ := eq8 X1 X2 X0
       grind)
    | (have i₁ := eq169 (M.op X2 X2) X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq169
    | (have j0 := eq169 X1 (M.op X2 X2)
       grind)
    | (have r₁ := eq169 (M.op (M.op X1 X1) (M.op X1 X1)) (M.op X1 X1)
       have r₂ := eq8 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | exact resolve eq169 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq206 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X2) X3) = (M.op X3 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X4 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq18 (M.op X1 X1) X4 X3 X2
       have i₂ := eq8 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq18 (M.op X0 X0) X4 X3 X2
       have i₂ := eq8 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op X4 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op (M.op X2 X2) (M.op X3 X3)) X4 X1
       have i₂ := eq18 X2 X3 (M.op X1 X1) X0
       grind)
    | (have i₁ := eq8 X2 X1 X3
       have i₂ := eq18 X0 X1 X2 X3
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq962 : ∀ X0 X1 X2 X3 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (M.op X2 X2) X3) = (M.op X3 (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq35 (σ X1) X3 X2 (σ X0)
       grind)
    | exact superpose eq35 eq13
    | (have j1 := eq35 (σ X1) X3 X2 X3
       grind)
    | exact resolve eq13 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1066 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 (σ X0)) = (M.op X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq171 X1 (σ X0) X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq171
    | (have j0 := eq171 X0 (σ X0) X2
       grind)
    | exact resolve eq171 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq1257 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ X0)
       have i₂ := eq39 X0 X0
       grind)
    | exact superpose eq39 eq11
    | (have j0 := eq11 X1 (σ X0)
       have j1 := eq39 X0 X0
       grind)
    | (have r₁ := eq11 X0 (σ X1)
       have r₂ := eq39 X0 X1
       grind)
    | exact resolve eq11 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1324 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq39 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq1328 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1257 X0 X1
       have j1 := eq11 X1 (σ X0)
       grind)
    | (have r₁ := eq1257 X0 X1
       have r₂ := eq11 X0 (σ X0)
       grind)
    | exact resolve eq1257 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257
  have eq1349 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1328 (τ X0) X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq1328
    | (have j0 := eq1328 (τ X0) X1
       grind)
    | exact resolve eq1328 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328
  have eq1357 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1349 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1349
    | (have j0 := eq1349 X0 X1
       grind)
    | exact resolve eq1349 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1349
  have eq1362 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1357 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1357
    | (have j0 := eq1357 X0 X1
       grind)
    | exact resolve eq1357 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357
  have eq1526 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1362 (τ X0) X1
       have i₂ := eq83 X0 X0
       grind)
    | exact superpose eq83 eq1362
    | (have j0 := eq1362 (τ X0) X1
       grind)
    | exact resolve eq1362 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq1362
  have eq1954 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq40 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq40
    | (have j0 := eq40 X0 X1
       grind)
    | exact resolve eq40 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq2074 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1954 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1954
    | (have j0 := eq1954 X0 X1
       grind)
    | exact resolve eq1954 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1954
  have eq3526 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1324 X0
       have i₂ := eq170 X1 X0 X0
       grind)
    | exact superpose eq170 eq1324
    | (have j0 := eq1324 X0
       have j1 := eq170 X1 X0 x
       grind)
    | exact resolve eq1324 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq3547 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1324 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq1324
    | (have j0 := eq1324 (τ X0)
       grind)
    | exact resolve eq1324 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324
  have eq3563 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3547 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3547
    | (have j0 := eq3547 X0
       grind)
    | exact resolve eq3547 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3547
  have eq3570 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3526 X0 X1
       have j1 := eq11 X1 (σ X0)
       grind)
    | (have r₁ := eq3526 X0 X1
       have r₂ := eq11 X0 (σ X0)
       grind)
    | exact resolve eq3526 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3526
  have eq3571 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3563 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3563
    | (have j0 := eq3563 X0
       grind)
    | exact resolve eq3563 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3563
  have eq3935 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3570 X0 X1
       have i₂ := eq2074 X2 X0
       grind)
    | exact superpose eq2074 eq3570
    | (have j0 := eq3570 X0 X1
       have j1 := eq2074 X2 X0
       grind)
    | exact resolve eq3570 eq2074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3570
  have eq3963 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3935 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3935
  have eq4882 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq164 x y X0
       grind)
    | exact superpose eq164 eq14
    | (have j1 := eq164 X0 y X0
       grind)
    | exact resolve eq14 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq4986 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq4882 X0
       have j1 := eq3963 y X0 x
       grind)
    | (have r₁ := eq4882 X0
       have r₂ := eq3963 y x x
       grind)
    | exact resolve eq4882 eq3963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3963 eq4882
  have eq5022 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3571 (σ y)
       have i₂ := eq4986 (σ y)
       grind)
    | exact superpose eq4986 eq3571
    | (have j0 := eq3571 (σ y)
       grind)
    | (have r₁ := eq3571 (σ y)
       have r₂ := eq4986 (σ y)
       grind)
    | exact resolve eq3571 eq4986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5024 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k X0 (τ (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1526 (σ y) X0
       have i₂ := eq4986 (σ y)
       grind)
    | exact superpose eq4986 eq1526
    | (have j0 := eq1526 (σ y) X0
       grind)
    | exact resolve eq1526 eq4986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526 eq4986
  have eq5049 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq5024 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5024
  have eq5051 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5022
  have eq5059 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq5049 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq5049
    | exact resolve eq5049 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5049
  have eq5213 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3571 y
       have i₂ := eq5059 y
       grind)
    | exact superpose eq5059 eq3571
    | (have j0 := eq3571 y
       grind)
    | (have r₁ := eq3571 y
       have r₂ := eq5059 y
       grind)
    | exact resolve eq3571 eq5059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5059
  have eq5239 : y = (M.op y y) := by grind
  clear eq5213
  have eq5389 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1 y
       have i₂ := eq5239
       grind)
    | exact superpose eq5239 eq19
    | exact resolve eq19 eq5239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5393 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1 y
       have i₂ := eq5239
       grind)
    | exact superpose eq5239 eq23
    | exact resolve eq23 eq5239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5396 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 X2)) = (M.op y (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 y X0 X1 X2
       have i₂ := eq5239
       grind)
    | exact superpose eq5239 eq24
    | exact resolve eq24 eq5239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq10348 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X0) (M.op X1 X1)) ≠ (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op X4 X4)) ∨ (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op X4 X4)) = (k (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op X4 X4)) (M.op X5 X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq174 X1 (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op X4 X4)) X5
       have i₂ := eq206 X2 X3 X0 (M.op X1 X1) X4
       grind)
    | (have i₁ := eq174 X2 X3 X2
       have i₂ := eq206 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq206 eq174
    | (have j0 := eq174 X0 (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op X4 X4)) X5
       grind)
    | (have r₁ := eq174 X0 (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) X2
       have r₂ := eq206 X0 X0 (M.op X0 X0) (M.op X0 X0) X0
       grind)
    | exact resolve eq174 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq206
  have eq10358 : ∀ X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op X4 X4)) = (k (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op X4 X4)) (M.op X5 X5)) := by
    intro X2 X3 X4 X5
    first
    | (have j0 := eq10348 x x X2 X3 X4 X5
       grind)
    | (have r₁ := eq10348 x x X2 X3 X4 X5
       have r₂ := eq263 x x X2 X3 X4
       grind)
    | (have r₁ := eq10348 (M.op X3 X3) X4 X2 X2 x X5
       have r₂ := eq263 (M.op X2 X2) x X3 X3 X4
       grind)
    | exact resolve eq10348 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263 eq10348
  have eq10656 : ∀ X2 X3 X5 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) y) = (k (M.op (M.op (M.op X2 X2) (M.op X3 X3)) y) (M.op X5 X5)) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq10358 X2 X3 x X5
       have i₂ := eq5393 (M.op (M.op X2 X2) (M.op X3 X3)) x
       grind)
    | exact superpose eq5393 eq10358
    | exact resolve eq10358 eq5393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10358
  have eq10954 : ∀ X2 X5 : G, (M.op (M.op (M.op X2 X2) y) y) = (k (M.op (M.op (M.op X2 X2) y) y) (M.op X5 X5)) := by
    intro X2 X5
    first
    | (have i₁ := eq10656 X2 x X5
       have i₂ := eq5393 (M.op X2 X2) x
       grind)
    | exact superpose eq5393 eq10656
    | exact resolve eq10656 eq5393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10656
  have eq11227 : ∀ X5 : G, (M.op (M.op y y) y) = (k (M.op (M.op y y) y) (M.op X5 X5)) := by
    intro X5
    first
    | (have i₁ := eq10954 x X5
       have i₂ := eq5389 x y
       grind)
    | exact superpose eq5389 eq10954
    | exact resolve eq10954 eq5389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10954
  have eq11485 : ∀ X5 : G, (M.op y y) = (k (M.op y y) (M.op X5 X5)) := by
    intro X5
    first
    | (have i₁ := eq11227 X5
       have i₂ := eq5389 y y
       grind)
    | exact superpose eq5389 eq11227
    | exact resolve eq11227 eq5389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11227
  have eq11672 : ∀ X5 : G, y = (k y (M.op X5 X5)) := by
    intro X5
    first
    | (have i₁ := eq11485 X5
       have i₂ := eq5239
       grind)
    | exact superpose eq5239 eq11485
    | exact resolve eq11485 eq5239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11485
  have eq20845 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 (σ y) X1
       have i₂ := eq5051
       grind)
    | exact superpose eq5051 eq8
    | exact resolve eq8 eq5051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20846 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 (σ y)
       have i₂ := eq5051
       grind)
    | exact superpose eq5051 eq8
    | exact resolve eq8 eq5051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20851 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1 (σ y)
       have i₂ := eq5051
       grind)
    | exact superpose eq5051 eq19
    | exact resolve eq19 eq5051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq20855 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1 (σ y)
       have i₂ := eq5051
       grind)
    | exact superpose eq5051 eq23
    | exact resolve eq23 eq5051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq20966 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq20855 X0 x
       have i₂ := eq5393 X0 x
       grind)
    | exact superpose eq5393 eq20855
    | exact resolve eq20855 eq5393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20855
  have eq20970 : ∀ X1 : G, (M.op (σ y) X1) = (M.op y X1) := by
    intro X1
    first
    | (have i₁ := eq20851 x X1
       have i₂ := eq5389 x X1
       grind)
    | exact superpose eq5389 eq20851
    | exact resolve eq20851 eq5389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20851
  have eq20974 : ∀ X0 : G, (M.op X0 y) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq20846 X0 x
       have i₂ := eq5393 X0 x
       grind)
    | exact superpose eq5393 eq20846
    | exact resolve eq20846 eq5393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20846
  have eq20975 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq20845 X0 x
       have i₂ := eq5389 x X0
       grind)
    | exact superpose eq5389 eq20845
    | exact resolve eq20845 eq5389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20845
  have eq33318 : (σ y) = (M.op (σ y) y) := by
    first
    | (have i₁ := eq5051
       have i₂ := eq20966 (σ y)
       grind)
    | exact superpose eq20966 eq5051
    | exact resolve eq5051 eq20966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5051
  have eq33323 : (σ y) = (M.op y y) := by
    first
    | (have i₁ := eq33318
       have i₂ := eq20970 y
       grind)
    | exact superpose eq20970 eq33318
    | exact resolve eq33318 eq20970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33318
  have eq33449 : y = (σ y) := by
    first
    | (have i₁ := eq33323
       have i₂ := eq5239
       grind)
    | exact superpose eq5239 eq33323
    | exact resolve eq33323 eq5239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33323
  have eq37817 : ∀ X0 : G, (k y (σ X0)) = (σ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq33449
       grind)
    | exact superpose eq33449 eq13
    | exact resolve eq13 eq33449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37831 : ∀ X0 : G, (k y (τ X0)) = (τ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq48 y X0
       have i₂ := eq33449
       grind)
    | exact superpose eq33449 eq48
    | exact resolve eq48 eq33449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq49366 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq20970 X0
       have i₂ := eq20974 X0
       grind)
    | exact superpose eq20974 eq20970
    | exact resolve eq20970 eq20974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20974
  have eq57136 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq20975 (σ x)
       grind)
    | exact superpose eq20975 eq14
    | exact resolve eq14 eq20975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20975
  have eq136390 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) ≠ (M.op (M.op X2 X2) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq962 X0 X1 X2 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq136391 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op y (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq136390 X0 X1 x
       have i₂ := eq5389 x (σ X0)
       grind)
    | exact superpose eq5389 eq136390
    | (have j0 := eq136390 X0 X1 x
       grind)
    | exact resolve eq136390 eq5389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5389 eq136390
  have eq144067 : ∀ X0 X1 : G, (M.op y (σ X0)) = (σ (k y X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1066 X0 X1 y
       have i₂ := eq37817 X0
       grind)
    | exact superpose eq37817 eq1066
    | (have j0 := eq1066 X0 X1 x
       grind)
    | exact resolve eq1066 eq37817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066 eq37817
  have eq147593 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op y X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq37831 X0
       have i₂ := eq12 y X0
       grind)
    | exact superpose eq12 eq37831
    | (have j1 := eq12 X0 X0
       grind)
    | exact resolve eq37831 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37831
  have eq645644 : ∀ X0 X1 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2074 y X0
       have i₂ := eq144067 X0 X1
       grind)
    | exact superpose eq144067 eq2074
    | (have j0 := eq2074 X0 X0
       have j1 := eq144067 X0 X1
       grind)
    | exact resolve eq2074 eq144067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2074 eq144067
  have eq645733 : ∀ X0 X1 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq645644 X0 X1
       have j1 := eq11 X1 X0
       grind)
    | (have r₁ := eq645644 X1 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq645644 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645644
  have eq649516 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op X0 y)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq147593 X0
       have i₂ := eq49366 X0
       grind)
    | (have i₁ := eq147593 y
       have i₂ := eq49366 y
       grind)
    | exact superpose eq49366 eq147593
    | (have j0 := eq147593 X0
       grind)
    | exact resolve eq147593 eq49366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147593
  have eq687104 : ∀ X0 X1 : G, (σ (M.op X0 y)) = (M.op y (σ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq645733 X0 X1
       have i₂ := eq49366 X0
       grind)
    | (have i₁ := eq645733 y X1
       have i₂ := eq49366 y
       grind)
    | exact superpose eq49366 eq645733
    | (have j0 := eq645733 X0 X1
       grind)
    | exact resolve eq645733 eq49366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49366 eq645733
  have eq689654 : ∀ X0 : G, (M.op X0 y) = (σ (k y (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 y)
       have i₂ := eq649516 X0
       grind)
    | exact superpose eq649516 eq10
    | (have j1 := eq649516 X0
       grind)
    | exact resolve eq10 eq649516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649516
  have eq689760 : ∀ X0 : G, (M.op X0 y) = (k (σ y) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq689654 X0
       have i₂ := eq16 X0 y
       grind)
    | exact superpose eq16 eq689654
    | (have j0 := eq689654 X0
       grind)
    | exact resolve eq689654 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq689654
  have eq689771 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq689760 X0
       have i₂ := eq33449
       grind)
    | exact superpose eq33449 eq689760
    | (have j0 := eq689760 X0
       grind)
    | exact resolve eq689760 eq33449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689760
  have eq690946 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op y (M.op X2 X2)) ∨ (M.op X0 y) = (k y X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5396 X2 X0 X1
       have i₂ := eq689771 X0
       grind)
    | exact superpose eq689771 eq5396
    | (have j1 := eq689771 X0
       grind)
    | exact resolve eq5396 eq689771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5396 eq689771
  have eq691052 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y y) ∨ (M.op X0 y) = (k y X0) := by
    intro X0 X1
    first
    | (have i₁ := eq690946 X0 X1 x
       have i₂ := eq5393 y x
       grind)
    | exact superpose eq5393 eq690946
    | (have j0 := eq690946 X0 X1 x
       grind)
    | exact resolve eq690946 eq5393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690946
  have eq691126 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = y ∨ (M.op X0 y) = (k y X0) := by
    intro X0 X1
    first
    | (have i₁ := eq691052 X0 X1
       have i₂ := eq5239
       grind)
    | exact superpose eq5239 eq691052
    | (have j0 := eq691052 X0 X1
       grind)
    | exact resolve eq691052 eq5239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691052
  have eq691171 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq691126 X0 x
       have i₂ := eq5393 X0 x
       grind)
    | exact superpose eq5393 eq691126
    | (have j0 := eq691126 X0 x
       grind)
    | exact resolve eq691126 eq5393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5393 eq691126
  have eq747433 : ∀ X0 : G, (σ y) ≠ (M.op y (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq136391 y (M.op x x)
       have i₂ := eq11672 x
       grind)
    | exact superpose eq11672 eq136391
    | exact resolve eq136391 eq11672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11672 eq136391
  have eq747442 : ∀ X0 : G, (σ y) ≠ (M.op y y) ∨ (σ y) = (M.op (σ y) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq747433 X0
       have i₂ := eq20966 y
       grind)
    | exact superpose eq20966 eq747433
    | (have j0 := eq747433 X0
       grind)
    | exact resolve eq747433 eq20966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20966 eq747433
  have eq747463 : ∀ X0 : G, y ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq747442 X0
       have i₂ := eq5239
       grind)
    | exact superpose eq5239 eq747442
    | (have j0 := eq747442 X0
       grind)
    | exact resolve eq747442 eq5239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5239 eq747442
  have eq747482 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq747463 X0
       grind)
    | (have r₁ := eq747463 X0
       have r₂ := eq33449
       grind)
    | exact resolve eq747463 eq33449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747463
  have eq747498 : ∀ X0 : G, (σ y) = (M.op y (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq747482 X0
       have i₂ := eq20970 (σ (M.op X0 X0))
       grind)
    | exact superpose eq20970 eq747482
    | exact resolve eq747482 eq20970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20970 eq747482
  have eq747507 : ∀ X0 : G, y = (M.op y (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq747498 X0
       have i₂ := eq33449
       grind)
    | exact superpose eq33449 eq747498
    | exact resolve eq747498 eq33449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747498
  have eq748235 : ∀ X0 : G, (M.op y (σ x)) ≠ (M.op y (σ x)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq57136
       have i₂ := eq687104 x X0
       grind)
    | exact superpose eq687104 eq57136
    | (have j1 := eq687104 x X0
       grind)
    | (have r₁ := eq57136
       have r₂ := eq687104 x x
       grind)
    | exact resolve eq57136 eq687104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687104
  have eq748260 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq748235 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748235
  have eq748418 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3571 x
       have i₂ := eq748260 x
       grind)
    | exact superpose eq748260 eq3571
    | (have j0 := eq3571 x
       grind)
    | (have r₁ := eq3571 x
       have r₂ := eq748260 x
       grind)
    | exact resolve eq3571 eq748260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3571
  have eq748715 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq691171 x
       have i₂ := eq748260 y
       grind)
    | exact superpose eq748260 eq691171
    | (have j0 := eq691171 x
       grind)
    | exact resolve eq691171 eq748260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691171 eq748260
  have eq748723 : y = (M.op x y) := by grind
  clear eq748715
  have eq748725 : x = (M.op x x) := by grind
  clear eq748418
  have eq749127 : (σ y) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq57136
       have i₂ := eq748723
       grind)
    | exact superpose eq748723 eq57136
    | exact resolve eq57136 eq748723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57136 eq748723
  have eq749179 : y ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq749127
       have i₂ := eq33449
       grind)
    | exact superpose eq33449 eq749127
    | exact resolve eq749127 eq33449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33449 eq749127
  have eq749418 : y = (M.op y (σ x)) := by
    first
    | (have i₁ := eq747507 x
       have i₂ := eq748725
       grind)
    | exact superpose eq748725 eq747507
    | exact resolve eq747507 eq748725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747507 eq748725
  have eq749430 : False := by grind
  exact eq749430
