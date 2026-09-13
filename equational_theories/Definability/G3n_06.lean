import equational_theories.Definability.AutBox3
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,X) = X then m(Y,X) else if X = Y then m(X,X) else if m(Y,Y) = Y then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_x_x_y_pyy_y_pyx_pxx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ a = b ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = a ∨ a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq62 (σ X0)
       grind)
    | exact superpose eq62 eq15
    | exact resolve eq15 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq65
    | exact resolve eq65 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq65
  have eq86 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq11
    | (have j0 := eq11 (σ X0) X1
       grind)
    | exact resolve eq11 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X1 (σ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq87
    | (have j0 := eq87 (σ X0) X1
       grind)
    | exact resolve eq87 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq248 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq235 X0 X1
       have i₂ := eq76 X1
       grind)
    | exact superpose eq76 eq235
    | (have j0 := eq235 X0 X1
       grind)
    | exact resolve eq235 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq256 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq248 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq248
    | (have j0 := eq248 X0 X1
       grind)
    | exact resolve eq248 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq463 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq256 x y
       grind)
    | exact superpose eq256 eq16
    | (have j1 := eq256 x y
       grind)
    | exact resolve eq16 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq1572 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq463
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq463
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq463
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq463
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq463 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq1573 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq1572
  have eq38390 : (M.op y y) = (τ (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq1573
       grind)
    | exact superpose eq1573 eq9
    | exact resolve eq9 eq1573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1573
  have eq38599 : y = (M.op y y) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq38390
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq38390
    | exact resolve eq38390 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38390
  have eq38600 : (σ x) = (σ (M.op x x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq38599
  have eq38607 : (M.op x x) = (τ (σ x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq38600
       grind)
    | exact superpose eq38600 eq9
    | exact resolve eq9 eq38600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38600
  have eq38816 : x = (M.op x x) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq38607
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq38607
    | exact resolve eq38607 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38607
  have eq38817 : y = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq38816
  have eq38818 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq11 y X0
       have i₂ := eq38817
       grind)
    | exact superpose eq38817 eq11
    | (have j0 := eq11 y X0
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq38817
       grind)
    | (have r₁ := eq11 x x
       have r₂ := eq38817
       grind)
    | exact resolve eq11 eq38817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38819 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq86 y X0
       have i₂ := eq38817
       grind)
    | exact superpose eq38817 eq86
    | (have j0 := eq86 y X0
       grind)
    | exact resolve eq86 eq38817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq38817
  have eq38844 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq38819 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38819
  have eq38845 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq38818 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38818
  have eq38919 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op (τ X0) y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq19 X0 y
       have i₂ := eq38845 (τ X0)
       grind)
    | exact superpose eq38845 eq19
    | exact resolve eq19 eq38845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq38845
  have eq39334 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k y X0)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq38844 (σ X0)
       have i₂ := eq15 y X0
       grind)
    | exact superpose eq15 eq38844
    | exact resolve eq38844 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38844
  have eq40490 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (M.op X0 y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq38919 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq38919
    | exact resolve eq38919 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38919
  have eq40656 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq40490 X0
       have i₂ := eq15 y X0
       grind)
    | exact superpose eq15 eq40490
    | exact resolve eq40490 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40490
  have eq41722 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq39334 x
       grind)
    | exact superpose eq39334 eq16
    | exact resolve eq16 eq39334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39334
  have eq41768 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq41722
       have r₂ := eq40656 x
       grind)
    | exact resolve eq41722 eq40656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40656 eq41722
  have eq41812 : ∀ X0 : G, x ≠ x ∨ x = X0 ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq87 X0 x
       have i₂ := eq41768
       grind)
    | exact superpose eq41768 eq87
    | (have j0 := eq87 x X0
       grind)
    | (have r₁ := eq87 X0 x
       have r₂ := eq41768
       grind)
    | exact resolve eq87 eq41768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq41814 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq105 x X0
       have i₂ := eq41768
       grind)
    | exact superpose eq41768 eq105
    | (have j0 := eq105 x X0
       grind)
    | exact resolve eq105 eq41768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq41768
  have eq41833 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq41814 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41814
  have eq41835 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq41812 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41812
  have eq43116 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op x (τ X0))) ∨ (τ X0) = x ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq18 X0 x
       have i₂ := eq41835 (τ X0)
       grind)
    | exact superpose eq41835 eq18
    | (have j1 := eq41835 (τ X0)
       grind)
    | exact resolve eq18 eq41835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq41835
  have eq51671 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ (σ X0) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq41833 (σ X0)
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq41833
    | (have j0 := eq41833 (σ X0)
       grind)
    | exact resolve eq41833 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41833
  have eq112386 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op x X0)) ∨ x = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq43116 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq43116
    | exact resolve eq43116 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43116
  have eq112702 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op x X0)) ∨ x = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq112386 X0
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq112386
    | (have j0 := eq112386 X0
       grind)
    | exact resolve eq112386 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112386
  have eq505745 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq51671 y
       grind)
    | exact superpose eq51671 eq16
    | (have j1 := eq51671 y
       grind)
    | exact resolve eq16 eq51671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51671
  have eq505792 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq505745
  have eq506008 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq505792
       have i₂ := eq112702 y
       grind)
    | exact superpose eq112702 eq505792
    | (have j1 := eq112702 y
       grind)
    | (have r₁ := eq505792
       have r₂ := eq112702 y
       grind)
    | exact resolve eq505792 eq112702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112702 eq505792
  have eq506011 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq506008
  have eq506012 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq506011
  have eq506021 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq506012
       grind)
    | exact superpose eq506012 eq9
    | exact resolve eq9 eq506012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506012
  have eq506922 : x = y ∨ x = y := by
    first
    | (have i₁ := eq506021
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq506021
    | exact resolve eq506021 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506021
  have eq506923 : x = y := by grind
  clear eq506922
  have eq506925 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq506923
       grind)
    | exact superpose eq506923 eq16
    | exact resolve eq16 eq506923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506923
  have eq506926 : False := by grind
  exact eq506926

/-- `x □ y = if m(X,X) = X then m(Y,X) else if X = Y then m(X,Y) else if m(Y,Y) = Y then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_x_x_y_pyy_y_pyx_pxy_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ a = b ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = a ∨ a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq62 (σ X0)
       grind)
    | exact superpose eq62 eq15
    | exact resolve eq15 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq65
    | exact resolve eq65 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq65
  have eq86 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq11
    | (have j0 := eq11 (σ X0) X1
       grind)
    | exact resolve eq11 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X1 (σ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq87
    | (have j0 := eq87 (σ X0) X1
       grind)
    | exact resolve eq87 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq248 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq235 X0 X1
       have i₂ := eq76 X1
       grind)
    | exact superpose eq76 eq235
    | (have j0 := eq235 X0 X1
       grind)
    | exact resolve eq235 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq256 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq248 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq248
    | (have j0 := eq248 X0 X1
       grind)
    | exact resolve eq248 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq463 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq256 x y
       grind)
    | exact superpose eq256 eq16
    | (have j1 := eq256 x y
       grind)
    | exact resolve eq16 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq1572 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq463
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq463
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq463
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq463
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq463 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq1573 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq1572
  have eq38390 : (M.op y y) = (τ (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq1573
       grind)
    | exact superpose eq1573 eq9
    | exact resolve eq9 eq1573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1573
  have eq38599 : y = (M.op y y) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq38390
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq38390
    | exact resolve eq38390 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38390
  have eq38600 : (σ x) = (σ (M.op x x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq38599
  have eq38607 : (M.op x x) = (τ (σ x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq38600
       grind)
    | exact superpose eq38600 eq9
    | exact resolve eq9 eq38600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38600
  have eq38816 : x = (M.op x x) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq38607
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq38607
    | exact resolve eq38607 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38607
  have eq38817 : y = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq38816
  have eq38818 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq11 y X0
       have i₂ := eq38817
       grind)
    | exact superpose eq38817 eq11
    | (have j0 := eq11 y X0
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq38817
       grind)
    | (have r₁ := eq11 x x
       have r₂ := eq38817
       grind)
    | exact resolve eq11 eq38817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38819 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq86 y X0
       have i₂ := eq38817
       grind)
    | exact superpose eq38817 eq86
    | (have j0 := eq86 y X0
       grind)
    | exact resolve eq86 eq38817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq38817
  have eq38844 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq38819 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38819
  have eq38845 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq38818 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38818
  have eq38919 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op (τ X0) y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq19 X0 y
       have i₂ := eq38845 (τ X0)
       grind)
    | exact superpose eq38845 eq19
    | exact resolve eq19 eq38845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq38845
  have eq39334 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k y X0)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq38844 (σ X0)
       have i₂ := eq15 y X0
       grind)
    | exact superpose eq15 eq38844
    | exact resolve eq38844 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38844
  have eq40490 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (M.op X0 y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq38919 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq38919
    | exact resolve eq38919 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38919
  have eq40656 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq40490 X0
       have i₂ := eq15 y X0
       grind)
    | exact superpose eq15 eq40490
    | exact resolve eq40490 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40490
  have eq41722 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq39334 x
       grind)
    | exact superpose eq39334 eq16
    | exact resolve eq16 eq39334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39334
  have eq41768 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq41722
       have r₂ := eq40656 x
       grind)
    | exact resolve eq41722 eq40656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40656 eq41722
  have eq41812 : ∀ X0 : G, x ≠ x ∨ x = X0 ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq87 X0 x
       have i₂ := eq41768
       grind)
    | exact superpose eq41768 eq87
    | (have j0 := eq87 x X0
       grind)
    | (have r₁ := eq87 X0 x
       have r₂ := eq41768
       grind)
    | exact resolve eq87 eq41768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq41814 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq105 x X0
       have i₂ := eq41768
       grind)
    | exact superpose eq41768 eq105
    | (have j0 := eq105 x X0
       grind)
    | exact resolve eq105 eq41768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq41768
  have eq41833 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq41814 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41814
  have eq41835 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq41812 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41812
  have eq43116 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op x (τ X0))) ∨ (τ X0) = x ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq18 X0 x
       have i₂ := eq41835 (τ X0)
       grind)
    | exact superpose eq41835 eq18
    | (have j1 := eq41835 (τ X0)
       grind)
    | exact resolve eq18 eq41835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq41835
  have eq51671 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ (σ X0) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq41833 (σ X0)
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq41833
    | (have j0 := eq41833 (σ X0)
       grind)
    | exact resolve eq41833 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41833
  have eq112386 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op x X0)) ∨ x = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq43116 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq43116
    | exact resolve eq43116 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43116
  have eq112702 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op x X0)) ∨ x = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq112386 X0
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq112386
    | (have j0 := eq112386 X0
       grind)
    | exact resolve eq112386 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112386
  have eq505745 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq51671 y
       grind)
    | exact superpose eq51671 eq16
    | (have j1 := eq51671 y
       grind)
    | exact resolve eq16 eq51671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51671
  have eq505792 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq505745
  have eq506008 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq505792
       have i₂ := eq112702 y
       grind)
    | exact superpose eq112702 eq505792
    | (have j1 := eq112702 y
       grind)
    | (have r₁ := eq505792
       have r₂ := eq112702 y
       grind)
    | exact resolve eq505792 eq112702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112702 eq505792
  have eq506011 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq506008
  have eq506012 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq506011
  have eq506021 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq506012
       grind)
    | exact superpose eq506012 eq9
    | exact resolve eq9 eq506012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506012
  have eq506922 : x = y ∨ x = y := by
    first
    | (have i₁ := eq506021
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq506021
    | exact resolve eq506021 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506021
  have eq506923 : x = y := by grind
  clear eq506922
  have eq506925 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq506923
       grind)
    | exact superpose eq506923 eq16
    | exact resolve eq16 eq506923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506923
  have eq506926 : False := by grind
  exact eq506926

/-- `x □ y = if m(X,X) = X then m(Y,X) else if X = Y then m(Y,X) else if m(Y,Y) = Y then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_x_x_y_pyy_y_pyx_pyx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ a = b ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = a ∨ a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
  have eq28 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 (k X0 X1) (M.op X1 X0)
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 (M.op X1 X0) (k X0 X1)
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       have j1 := eq28 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq29 X0 X1
       have r₂ := eq28 X0 X1
       grind)
    | (have r₁ := eq29 X1 X0
       have r₂ := eq28 X0 X1
       grind)
    | (have r₁ := eq29 X0 X1
       have r₂ := eq28 (k X0 X1) (M.op X1 X0)
       grind)
    | exact resolve eq29 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq32 : x = (τ (σ x)) := by
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
  have eq34 : y = (τ (σ y)) := by
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
  have eq42 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq43 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq62 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq16 (k X0 x)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq16
    | exact resolve eq16 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq16 (k X0 y)
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq62 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq62
    | exact resolve eq62 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq155 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq75 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq75
    | exact resolve eq75 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq177 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq178 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq177 X0
       grind)
    | exact superpose eq177 eq14
    | (have j0 := eq14 X0 X1
       grind)
    | exact resolve eq14 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 X0
       have i₂ := eq177 X0
       grind)
    | exact superpose eq177 eq30
    | (have j0 := eq30 X1 X0
       grind)
    | exact resolve eq30 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq531 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq178 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq178
    | (have j0 := eq178 (σ X0) X1
       grind)
    | exact resolve eq178 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq533 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq530 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq530
    | (have j0 := eq530 (σ X0) X1
       grind)
    | exact resolve eq530 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq979 : (M.op x y) = (k x y) ∨ x = y ∨ y = (M.op y y) ∨ x = (M.op x x) := by
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
  have eq980 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq985 : (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq980
       have i₂ := eq177 sF3
       grind)
    | exact superpose eq177 eq980
    | exact resolve eq980 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980
  have eq986 : y = (k y y) ∨ (M.op x y) = (k x y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq979
       have i₂ := eq177 y
       grind)
    | exact superpose eq177 eq979
    | exact resolve eq979 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979
  have eq989 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq985
       have i₂ := eq177 sF2
       grind)
    | exact superpose eq177 eq985
    | exact resolve eq985 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq990 : (M.op x y) = (k x y) ∨ y = (k y y) ∨ x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq986
       have i₂ := eq177 x
       grind)
    | exact superpose eq177 eq986
    | exact resolve eq986 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq2946 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq43 x
       have i₂ := eq990
       grind)
    | exact superpose eq990 eq43
    | exact resolve eq43 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq990
  have eq2947 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq2946
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2946
    | exact resolve eq2946 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2946
  have eq2950 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq20 eq2947
    | exact resolve eq2947 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2947
  have eq20771 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq2950 eq989
    | exact resolve eq989 eq2950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989 eq2950
  have eq20778 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ x = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq20771
       have r₂ := eq27
       grind)
    | exact resolve eq20771 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20771
  have eq20788 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq20778 eq155
    | exact resolve eq155 eq20778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq20778
  have eq20803 : y = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq34 eq20788
    | exact resolve eq20788 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20788
  have eq20804 : (σ x) = (k (σ x) (σ x)) ∨ y = (k y y) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y := by grind
  clear eq20803
  have eq20817 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (k y y) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq20804 eq144
    | exact resolve eq144 eq20804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq20804
  have eq20832 : x = (k x x) ∨ y = (k y y) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq32 eq20817
    | exact resolve eq20817 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20817
  have eq20833 : y = (k y y) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20832
  have eq20850 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq531 y X0
       have i₂ := eq20833
       grind)
    | exact superpose eq20833 eq531
    | (have j0 := eq531 y X0
       grind)
    | exact resolve eq531 eq20833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq20852 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq178 y X0
       have i₂ := eq20833
       grind)
    | exact superpose eq20833 eq178
    | (have j0 := eq178 y X0
       grind)
    | (have r₁ := eq178 y x
       have r₂ := eq20833
       grind)
    | (have r₁ := eq178 x x
       have r₂ := eq20833
       grind)
    | exact resolve eq178 eq20833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq20833
  have eq20853 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq20852 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20852
  have eq20855 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq20850 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20850
  have eq20859 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq20855 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20855
    | (have j0 := eq20855 X0
       grind)
    | exact resolve eq20855 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20855
  have eq20932 : (M.op x y) = (k y x) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq20853 x
       grind)
    | exact superpose eq20853 eq18
    | (have j1 := eq20853 x
       grind)
    | exact resolve eq18 eq20853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20853
  have eq21083 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq42 y
       have i₂ := eq20932
       grind)
    | exact superpose eq20932 eq42
    | exact resolve eq42 eq20932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20932
  have eq21084 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq21083
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21083
    | exact resolve eq21083 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21083
  have eq21089 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq21084
    | exact resolve eq21084 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21084
  have eq21116 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20859 eq26
    | (have j1 := eq20859 (σ x)
       grind)
    | exact resolve eq26 eq20859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20859
  have eq21117 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21089 eq21116
    | exact resolve eq21116 eq21089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21089 eq21116
  have eq21123 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq21117
       have r₂ := eq27
       grind)
    | exact resolve eq21117 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21117
  have eq21133 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq533 x X0
       have i₂ := eq21123
       grind)
    | exact superpose eq21123 eq533
    | (have j0 := eq533 x X0
       grind)
    | exact resolve eq533 eq21123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq21135 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq530 x X0
       have i₂ := eq21123
       grind)
    | exact superpose eq21123 eq530
    | (have j0 := eq530 x X0
       grind)
    | (have r₁ := eq530 x x
       have r₂ := eq21123
       grind)
    | exact resolve eq530 eq21123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq21123
  have eq21138 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq21135 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21135
  have eq21140 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq21133 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21133
  have eq21144 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq21140 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21140
    | (have j0 := eq21140 X0
       grind)
    | exact resolve eq21140 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21140
  have eq21184 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq21138 y
       grind)
    | exact superpose eq21138 eq18
    | (have j1 := eq21138 y
       grind)
    | exact resolve eq18 eq21138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21138
  have eq21196 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq42 y
       have i₂ := eq21184
       grind)
    | exact superpose eq21184 eq42
    | exact resolve eq42 eq21184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21184
  have eq21197 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq21196
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21196
    | exact resolve eq21196 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21196
  have eq21202 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq21197
    | exact resolve eq21197 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21197
  have eq21226 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21144 eq26
    | (have j1 := eq21144 (σ y)
       grind)
    | exact resolve eq26 eq21144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21144
  have eq21233 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21202 eq21226
    | exact resolve eq21226 eq21202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21202 eq21226
  have eq21237 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq21233
       have r₂ := eq27
       grind)
    | exact resolve eq21233 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21233
  have eq21241 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq21237 eq34
    | exact resolve eq34 eq21237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq21237
  have eq21334 : x = y ∨ x = y := by
    first
    | exact superpose eq32 eq21241
    | exact resolve eq21241 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq21241
  have eq21335 : x = y := by grind
  clear eq21334
  have eq21337 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq21335
       grind)
    | exact superpose eq21335 eq18
    | exact resolve eq18 eq21335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq21338 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq21335
       grind)
    | exact superpose eq21335 eq24
    | exact resolve eq24 eq21335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq21335
  have eq21387 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq21338
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21338
    | exact resolve eq21338 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21338
  have eq21388 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq21337
       have i₂ := eq177 x
       grind)
    | exact superpose eq177 eq21337
    | exact resolve eq21337 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21337
  have eq21389 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21387 eq26
    | exact resolve eq26 eq21387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq21387
  have eq21483 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq21389
       have i₂ := eq177 sF2
       grind)
    | exact superpose eq177 eq21389
    | exact resolve eq21389 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq21389
  have eq21491 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq42 x
       have i₂ := eq21388
       grind)
    | exact superpose eq21388 eq42
    | exact resolve eq42 eq21388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq21388
  have eq21500 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq21491
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21491
    | exact resolve eq21491 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq21491
  have eq21508 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21483 eq21500
    | exact resolve eq21500 eq21483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21483 eq21500
  have eq21516 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq21508
    | exact resolve eq21508 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq21508
  have eq21518 : False := by grind
  exact eq21518

/-- `x □ y = if m(X,X) = X then m(Y,X) else if X = Y then m(Y,Y) else if m(Y,Y) = Y then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_x_x_y_pyy_y_pyx_pyy_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ a = b ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = a ∨ a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq62 (σ X0)
       grind)
    | exact superpose eq62 eq15
    | exact resolve eq15 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq65
    | exact resolve eq65 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq65
  have eq86 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq11
    | (have j0 := eq11 (σ X0) X1
       grind)
    | exact resolve eq11 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X1 (σ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq87
    | (have j0 := eq87 (σ X0) X1
       grind)
    | exact resolve eq87 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq248 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq235 X0 X1
       have i₂ := eq76 X1
       grind)
    | exact superpose eq76 eq235
    | (have j0 := eq235 X0 X1
       grind)
    | exact resolve eq235 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq256 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq248 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq248
    | (have j0 := eq248 X0 X1
       grind)
    | exact resolve eq248 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq463 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq256 x y
       grind)
    | exact superpose eq256 eq16
    | (have j1 := eq256 x y
       grind)
    | exact resolve eq16 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq1572 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq463
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq463
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq463
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq463
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq463 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq1573 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq1572
  have eq38390 : (M.op y y) = (τ (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq1573
       grind)
    | exact superpose eq1573 eq9
    | exact resolve eq9 eq1573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1573
  have eq38599 : y = (M.op y y) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq38390
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq38390
    | exact resolve eq38390 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38390
  have eq38600 : (σ x) = (σ (M.op x x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq38599
  have eq38607 : (M.op x x) = (τ (σ x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq38600
       grind)
    | exact superpose eq38600 eq9
    | exact resolve eq9 eq38600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38600
  have eq38816 : x = (M.op x x) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq38607
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq38607
    | exact resolve eq38607 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38607
  have eq38817 : y = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq38816
  have eq38818 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq11 y X0
       have i₂ := eq38817
       grind)
    | exact superpose eq38817 eq11
    | (have j0 := eq11 y X0
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq38817
       grind)
    | (have r₁ := eq11 x x
       have r₂ := eq38817
       grind)
    | exact resolve eq11 eq38817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38819 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq86 y X0
       have i₂ := eq38817
       grind)
    | exact superpose eq38817 eq86
    | (have j0 := eq86 y X0
       grind)
    | exact resolve eq86 eq38817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq38817
  have eq38844 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq38819 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38819
  have eq38845 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq38818 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38818
  have eq38919 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op (τ X0) y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq19 X0 y
       have i₂ := eq38845 (τ X0)
       grind)
    | exact superpose eq38845 eq19
    | exact resolve eq19 eq38845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq38845
  have eq39334 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k y X0)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq38844 (σ X0)
       have i₂ := eq15 y X0
       grind)
    | exact superpose eq15 eq38844
    | exact resolve eq38844 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38844
  have eq40490 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (M.op X0 y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq38919 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq38919
    | exact resolve eq38919 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38919
  have eq40656 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq40490 X0
       have i₂ := eq15 y X0
       grind)
    | exact superpose eq15 eq40490
    | exact resolve eq40490 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40490
  have eq41722 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq39334 x
       grind)
    | exact superpose eq39334 eq16
    | exact resolve eq16 eq39334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39334
  have eq41768 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq41722
       have r₂ := eq40656 x
       grind)
    | exact resolve eq41722 eq40656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40656 eq41722
  have eq41812 : ∀ X0 : G, x ≠ x ∨ x = X0 ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq87 X0 x
       have i₂ := eq41768
       grind)
    | exact superpose eq41768 eq87
    | (have j0 := eq87 x X0
       grind)
    | (have r₁ := eq87 X0 x
       have r₂ := eq41768
       grind)
    | exact resolve eq87 eq41768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq41814 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq105 x X0
       have i₂ := eq41768
       grind)
    | exact superpose eq41768 eq105
    | (have j0 := eq105 x X0
       grind)
    | exact resolve eq105 eq41768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq41768
  have eq41833 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq41814 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41814
  have eq41835 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq41812 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41812
  have eq43116 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op x (τ X0))) ∨ (τ X0) = x ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq18 X0 x
       have i₂ := eq41835 (τ X0)
       grind)
    | exact superpose eq41835 eq18
    | (have j1 := eq41835 (τ X0)
       grind)
    | exact resolve eq18 eq41835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq41835
  have eq51671 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ (σ X0) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq41833 (σ X0)
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq41833
    | (have j0 := eq41833 (σ X0)
       grind)
    | exact resolve eq41833 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41833
  have eq112386 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op x X0)) ∨ x = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq43116 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq43116
    | exact resolve eq43116 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43116
  have eq112702 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op x X0)) ∨ x = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq112386 X0
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq112386
    | (have j0 := eq112386 X0
       grind)
    | exact resolve eq112386 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112386
  have eq505745 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq51671 y
       grind)
    | exact superpose eq51671 eq16
    | (have j1 := eq51671 y
       grind)
    | exact resolve eq16 eq51671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51671
  have eq505792 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq505745
  have eq506008 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq505792
       have i₂ := eq112702 y
       grind)
    | exact superpose eq112702 eq505792
    | (have j1 := eq112702 y
       grind)
    | (have r₁ := eq505792
       have r₂ := eq112702 y
       grind)
    | exact resolve eq505792 eq112702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112702 eq505792
  have eq506011 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq506008
  have eq506012 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq506011
  have eq506021 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq506012
       grind)
    | exact superpose eq506012 eq9
    | exact resolve eq9 eq506012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506012
  have eq506922 : x = y ∨ x = y := by
    first
    | (have i₁ := eq506021
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq506021
    | exact resolve eq506021 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506021
  have eq506923 : x = y := by grind
  clear eq506922
  have eq506925 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq506923
       grind)
    | exact superpose eq506923 eq16
    | exact resolve eq16 eq506923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506923
  have eq506926 : False := by grind
  exact eq506926

/-- `x □ y = if m(X,X) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,Y) = X then m(X,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_y_pxy_pyx_pyy_x_pxy_pxy_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = M.op b a ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = b ∨ M.op a b = M.op b a ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24
    | exact resolve eq24 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq24
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq24 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X1 : G, (M.op (M.op X1 X1) (M.op X1 X1)) = X1 ∨ (M.op (M.op X1 X1) X1) = (k (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq75 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  clear eq62
  have eq80 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq75 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq83 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq20 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq80 (τ X0)
       grind)
    | exact superpose eq80 eq20
    | exact resolve eq20 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq103 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq34
  have eq105 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq103 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq114 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq31 X0 (σ X0)
       have i₂ := eq105 (σ X0)
       grind)
    | exact superpose eq105 eq31
    | exact resolve eq31 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq105 (τ X0)
       grind)
    | exact superpose eq105 eq35
    | exact resolve eq35 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq105 (τ X0)
       grind)
    | exact superpose eq105 eq19
    | exact resolve eq19 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq116 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq116
    | exact resolve eq116 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq118 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq115 X0
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq115
    | exact resolve eq115 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq119 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq114 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq114
    | exact resolve eq114 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq126 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq117 X0
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq117
    | exact resolve eq117 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq127 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq119 X0
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq119
    | exact resolve eq119 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq119
  have eq131 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq126 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq126
    | exact resolve eq126 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq335 : ∀ X0 : G, (k X0 (σ (τ (M.op X0 X0)))) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq118 X0
       grind)
    | exact superpose eq118 eq25
    | exact resolve eq25 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq336 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq335 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq335
    | exact resolve eq335 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq337 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    grind
  clear eq336
  have eq338 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X0 (τ (M.op (σ X0) (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq337 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq337
    | exact resolve eq337 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq369 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq338 X0
       have i₂ := eq127 X0
       grind)
    | exact superpose eq127 eq338
    | exact resolve eq338 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq373 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq369 X0
       have i₂ := eq131 X0
       grind)
    | exact superpose eq131 eq369
    | exact resolve eq369 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq375 : ∀ X0 : G, (σ (M.op (τ (M.op X0 X0)) (τ X0))) = (k (σ (τ (M.op X0 X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq118 X0
       grind)
    | exact superpose eq118 eq83
    | exact resolve eq83 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq118
  have eq376 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq375 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq375
    | exact resolve eq375 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq377 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq376 X0
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq376
    | exact resolve eq376 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq376
  have eq383 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (τ (M.op (σ X0) (σ X0))) X0)) := by
    intro X0
    first
    | (have i₁ := eq377 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq377
    | exact resolve eq377 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq407 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq383 X0
       have i₂ := eq127 X0
       grind)
    | exact superpose eq127 eq383
    | exact resolve eq383 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq383
  have eq411 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq407 X0
       have i₂ := eq131 X0
       grind)
    | exact superpose eq131 eq407
    | exact resolve eq407 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq3702 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ (M.op X0 X0)) = X1 ∨ (M.op (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq131 X0
       grind)
    | exact superpose eq131 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq3800 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) ∨ (σ (M.op (τ X0) (τ X0))) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3702 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3702
    | (have j0 := eq3702 (τ X0) X1
       grind)
    | exact resolve eq3702 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3702
  have eq3887 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (σ (M.op (τ X0) (τ X0))) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3800 X0 X1
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq3800
    | (have j0 := eq3800 X0 X1
       grind)
    | exact resolve eq3800 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3800
  have eq3897 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3887 X0 X1
       have i₂ := eq126 X0
       grind)
    | exact superpose eq126 eq3887
    | (have j0 := eq3887 X0 X1
       grind)
    | exact resolve eq3887 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3887
  have eq18506 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3897 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3897
    | (have j0 := eq3897 (σ X1) (σ X0)
       grind)
    | exact resolve eq3897 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3897
  have eq18782 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18506 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq18506
    | (have j0 := eq18506 X0 X1
       grind)
    | exact resolve eq18506 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18506
  have eq18804 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18782 X0 X1
       have i₂ := eq131 X1
       grind)
    | exact superpose eq131 eq18782
    | (have j0 := eq18782 X0 X1
       grind)
    | exact resolve eq18782 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18782
  have eq18805 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18804 X0 X1
       have i₂ := eq131 X0
       grind)
    | exact superpose eq131 eq18804
    | (have j0 := eq18804 X0 X1
       grind)
    | exact resolve eq18804 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18804
  have eq554507 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq18805 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq18805 X0 X1
       grind)
    | exact superpose eq18805 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq18805 X1 X0
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq18805 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq18805 X0 X1
       grind)
    | exact resolve eq12 eq18805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18805
  have eq554510 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq554507 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554507
  have eq554563 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq554510 X0 X1
       have i₂ := eq131 X1
       grind)
    | exact superpose eq131 eq554510
    | (have j0 := eq554510 X0 X1
       grind)
    | exact resolve eq554510 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554510
  have eq554564 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq554563 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554563
  have eq554618 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq554564 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq554564
    | (have j0 := eq554564 X0 X1
       grind)
    | exact resolve eq554564 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554564
  have eq1310564 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op X1 X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq554618 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq554618
    | (have j0 := eq554618 X1 (τ X0)
       grind)
    | exact resolve eq554618 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554618
  have eq1311870 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op X1 X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1310564 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq1310564
    | (have j0 := eq1310564 X0 X1
       grind)
    | exact resolve eq1310564 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1310564
  have eq1312264 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) ∨ (σ (M.op X1 X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1311870 X0 X1
       have i₂ := eq126 X0
       grind)
    | exact superpose eq126 eq1311870
    | (have j0 := eq1311870 X0 X1
       grind)
    | exact resolve eq1311870 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1311870
  have eq1313248 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) ∨ (σ (M.op X0 X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X0
       have i₂ := eq1312264 X1 X0
       grind)
    | exact superpose eq1312264 eq24
    | (have j1 := eq1312264 X1 X0
       grind)
    | exact resolve eq24 eq1312264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1313519 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k (τ (σ X1)) X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 (σ X0)
       have i₂ := eq1312264 (σ X1) X0
       grind)
    | exact superpose eq1312264 eq31
    | (have j1 := eq1312264 (σ X1) X0
       grind)
    | exact resolve eq31 eq1312264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1312264
  have eq1314122 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1313248 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313248
  have eq1314447 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k (τ (σ X1)) X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1313519 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1313519
    | (have j0 := eq1313519 X0 X1
       grind)
    | exact resolve eq1313519 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313519
  have eq1314700 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k (τ (σ X1)) X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1314447 X0 X1
       have i₂ := eq131 X1
       grind)
    | exact superpose eq131 eq1314447
    | (have j0 := eq1314447 X0 X1
       grind)
    | exact resolve eq1314447 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq1314447
  have eq1314878 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1314700 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq1314700
    | (have j0 := eq1314700 X0 X1
       grind)
    | exact resolve eq1314700 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314700
  have eq1314879 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1314878 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314878
  have eq1314986 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1314122 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1314122
    | (have j0 := eq1314122 (τ X0) X1
       grind)
    | exact resolve eq1314122 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314122
  have eq1316865 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1314986 X0 X1
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq1314986
    | (have j0 := eq1314986 X0 X1
       grind)
    | exact resolve eq1314986 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1314986
  have eq1317107 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1316865 X0 X1
       have i₂ := eq126 X0
       grind)
    | exact superpose eq126 eq1316865
    | (have j0 := eq1316865 X0 X1
       grind)
    | exact resolve eq1316865 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq1316865
  have eq1319505 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq1317107 X0 X1
       grind)
    | exact superpose eq1317107 eq10
    | (have j1 := eq1317107 X0 X1
       grind)
    | exact resolve eq10 eq1317107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1317107
  have eq1320682 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1319505 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq1319505
    | (have j0 := eq1319505 X0 X1
       grind)
    | exact resolve eq1319505 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319505
  have eq1394671 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (σ X1) (σ X0))
       have i₂ := eq1314879 X1 X0
       grind)
    | exact superpose eq1314879 eq10
    | (have j1 := eq1314879 X1 X0
       grind)
    | exact resolve eq10 eq1314879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314879
  have eq1400968 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1394671 y x
       grind)
    | exact superpose eq1394671 eq16
    | (have j1 := eq1394671 y x
       grind)
    | exact resolve eq16 eq1394671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1394671
  have eq1402467 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1400968
       have i₂ := eq1320682 x y
       grind)
    | exact superpose eq1320682 eq1400968
    | (have j1 := eq1320682 x y
       grind)
    | exact resolve eq1400968 eq1320682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320682 eq1400968
  have eq1402479 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq1402467
  have eq1409241 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq373 x
       have i₂ := eq1402479
       grind)
    | exact superpose eq1402479 eq373
    | exact resolve eq373 eq1402479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402479
  have eq1409390 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq1409241
       have r₂ := eq16
       grind)
    | exact resolve eq1409241 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409241
  have eq1410551 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq411 y
       have i₂ := eq1409390
       grind)
    | exact superpose eq1409390 eq411
    | exact resolve eq411 eq1409390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409390
  have eq1410696 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1410551
       have r₂ := eq16
       grind)
    | exact resolve eq1410551 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410551
  have eq1411752 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq1410696
       grind)
    | exact superpose eq1410696 eq9
    | exact resolve eq9 eq1410696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410696
  have eq1412422 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1411752
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1411752
    | exact resolve eq1411752 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411752
  have eq1415997 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq373 x
       have i₂ := eq1412422
       grind)
    | exact superpose eq1412422 eq373
    | exact resolve eq373 eq1412422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373 eq1412422
  have eq1416145 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1415997
       have r₂ := eq16
       grind)
    | exact resolve eq1415997 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1415997
  have eq1417204 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq1416145
       grind)
    | exact superpose eq1416145 eq9
    | exact resolve eq9 eq1416145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1416145
  have eq1417874 : x = (M.op y y) := by
    first
    | (have i₁ := eq1417204
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq1417204
    | exact resolve eq1417204 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417204
  have eq1421405 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq411 y
       have i₂ := eq1417874
       grind)
    | exact superpose eq1417874 eq411
    | exact resolve eq411 eq1417874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411 eq1417874
  have eq1421550 : False := by grind
  exact eq1421550

/-- `x □ y = if m(X,X) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else if m(Y,Y) = X then m(X,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_y_pxy_pyx_pyy_x_pxy_pyx_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = M.op b a ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = b ∨ M.op a b = M.op b a ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 (M.op X1 X1)
       have r₂ := eq13 X1 X1
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | exact superpose eq14 eq28
    | (have j0 := eq28 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq28 X0 X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq28 (k X1 X1) X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq28 X0 X0
       have r₂ := eq14 X0 (k X0 X0)
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq32 : x = (τ (σ x)) := by
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
  have eq34 : y = (τ (σ y)) := by
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
  have eq38 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq39 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq42 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq43 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq47 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq16 (k x X0)
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq50 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq16 (k y X0)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq100 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq47
    | (have j0 := eq47 x
       grind)
    | exact resolve eq47 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq118 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq177 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq14 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : (M.op x y) = (k y x) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq29 y x
       grind)
    | exact superpose eq29 eq18
    | (have j1 := eq29 y x
       grind)
    | exact resolve eq18 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq29 sF3 sF2
       grind)
    | exact superpose eq29 eq26
    | (have j1 := eq29 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1054 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1056 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1054 X0
       have j1 := eq14 X0 X0
       grind)
    | (have r₁ := eq1054 x
       have r₂ := eq14 x x
       grind)
    | (have r₁ := eq1054 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | (have r₁ := eq1054 X0
       have r₂ := eq14 X0 (k X0 X0)
       grind)
    | exact resolve eq1054 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054
  have eq1058 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) ∨ (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq30 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq1060 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1058 X0
       have i₂ := eq1056 X0
       grind)
    | exact superpose eq1056 eq1058
    | (have j0 := eq1058 X0
       grind)
    | exact resolve eq1058 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058
  have eq1062 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (M.op (k X0 X0) X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1060 X0
       have i₂ := eq1056 X0
       grind)
    | exact superpose eq1056 eq1060
    | (have j0 := eq1060 X0
       grind)
    | exact resolve eq1060 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060
  have eq1064 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq177 X0
       have i₂ := eq1056 X0
       grind)
    | exact superpose eq1056 eq177
    | exact resolve eq177 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq1066 : ∀ X0 : G, (k (σ X0) (σ (k X0 X0))) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1064 (σ x)
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1064
    | exact resolve eq1064 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1071 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1066 X0
       have i₂ := eq10 X0 (k X0 X0)
       grind)
    | exact superpose eq10 eq1066
    | exact resolve eq1066 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066
  have eq2760 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq42 y
       have i₂ := eq180
       grind)
    | exact superpose eq180 eq42
    | exact resolve eq42 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq180
  have eq2761 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2760
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2760
    | exact resolve eq2760 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2760
  have eq2763 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq2761
    | exact resolve eq2761 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2761
  have eq2765 : y = (k x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2763
       have i₂ := eq1056 x
       grind)
    | exact superpose eq1056 eq2763
    | exact resolve eq2763 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2763
  have eq2767 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq2765
       have i₂ := eq1056 y
       grind)
    | exact superpose eq1056 eq2765
    | exact resolve eq2765 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2765
  have eq6534 : ∀ X0 : G, (k X0 (k X0 X0)) ≠ (M.op X0 (k X0 X0)) ∨ (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 (k X0 X0)) = (k (k X0 X0) X0) ∨ (M.op (k X0 X0) X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq13 (k X0 X0) X0
       have i₂ := eq1062 X0
       grind)
    | exact superpose eq1062 eq13
    | (have j0 := eq13 (k X0 X0) X0
       have j1 := eq1062 X0
       grind)
    | exact resolve eq13 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6535 : ∀ X0 : G, (k X0 (k X0 X0)) ≠ (k (k X0 X0) X0) ∨ (M.op (k X0 X0) X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq1062 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq6536 : ∀ X0 : G, (k X0 (k X0 X0)) ≠ (M.op X0 (k X0 X0)) ∨ (M.op X0 (k X0 X0)) = (k (k X0 X0) X0) ∨ (M.op (k X0 X0) X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq6534 X0
       have j1 := eq14 (k X0 X0) X0
       grind)
    | (have r₁ := eq6534 X0
       have r₂ := eq14 X0 (k X0 X0)
       grind)
    | (have r₁ := eq6534 x
       have r₂ := eq14 (k x x) x
       grind)
    | (have r₁ := eq6534 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op (k (M.op X0 X0) (M.op X0 X0)) (k (M.op X0 X0) (M.op X0 X0)))
       grind)
    | exact resolve eq6534 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6534
  have eq6539 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (k X0 X0) X0) ∨ (M.op (k X0 X0) X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq6536 X0
       grind)
    | (have r₁ := eq6536 X0
       have r₂ := eq1064 X0
       grind)
    | exact resolve eq6536 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6536
  have eq6542 : ∀ X0 : G, (k X0 (k X0 X0)) = (k (k X0 X0) X0) ∨ (M.op (k X0 X0) X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq6539 X0
       have i₂ := eq1064 X0
       grind)
    | exact superpose eq1064 eq6539
    | (have j0 := eq6539 X0
       grind)
    | exact resolve eq6539 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6539
  have eq6543 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq6542 X0
       have j1 := eq6535 X0
       grind)
    | (have r₁ := eq6542 X0
       have r₂ := eq6535 X0
       grind)
    | exact resolve eq6542 eq6535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6535 eq6542
  have eq6544 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq6543 (σ x)
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq6543
    | exact resolve eq6543 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6552 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq6544 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq6544
    | exact resolve eq6544 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6544
  have eq16267 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | exact superpose eq2767 eq181
    | exact resolve eq181 eq2767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq2767
  have eq16274 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | (have r₁ := eq16267
       have r₂ := eq27
       grind)
    | exact resolve eq16267 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16267
  have eq16280 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq16274
       have i₂ := eq1056 sF2
       grind)
    | exact superpose eq1056 eq16274
    | exact resolve eq16274 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16274
  have eq16282 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq16280
       have i₂ := eq1056 sF3
       grind)
    | exact superpose eq1056 eq16280
    | exact resolve eq16280 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056 eq16280
  have eq16286 : (τ (σ y)) = (k x x) ∨ (σ x) = (k (σ y) (σ y)) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | exact superpose eq16282 eq100
    | exact resolve eq100 eq16282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq16282
  have eq16311 : y = (k x x) ∨ (σ x) = (k (σ y) (σ y)) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | exact superpose eq34 eq16286
    | exact resolve eq16286 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq16286
  have eq16312 : (σ x) = (k (σ y) (σ y)) ∨ y = (k x x) ∨ x = (k y y) := by grind
  clear eq16311
  have eq16326 : (τ (σ x)) = (k y y) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | exact superpose eq16312 eq118
    | exact resolve eq118 eq16312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq16312
  have eq16351 : x = (k y y) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | exact superpose eq32 eq16326
    | exact resolve eq16326 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq16326
  have eq16352 : y = (k x x) ∨ x = (k y y) := by grind
  clear eq16351
  have eq16373 : (M.op x y) = (k x y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq1064 x
       have i₂ := eq16352
       grind)
    | exact superpose eq16352 eq1064
    | exact resolve eq1064 eq16352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq16376 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq1071 x
       have i₂ := eq16352
       grind)
    | exact superpose eq16352 eq1071
    | exact resolve eq1071 eq16352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071 eq16352
  have eq16382 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq16376
       have i₂ := eq43 x
       grind)
    | exact superpose eq43 eq16376
    | exact resolve eq16376 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16376
  have eq16383 : (M.op x y) = (k x y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq16373
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16373
    | exact resolve eq16373 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16373
  have eq16392 : (k (σ x) (σ y)) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq16382
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16382
    | exact resolve eq16382 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16382
  have eq16397 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq16392
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16392
    | exact resolve eq16392 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16392
  have eq16400 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq26 eq16397
    | exact resolve eq16397 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16397
  have eq16465 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ x = (k y y) := by
    first
    | exact superpose eq16400 eq101
    | exact resolve eq101 eq16400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16400
  have eq16470 : x = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq16383 eq16465
    | exact resolve eq16465 eq16383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16383 eq16465
  have eq16488 : (M.op x y) = (k x y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq6543 y
       have i₂ := eq16470
       grind)
    | exact superpose eq16470 eq6543
    | exact resolve eq6543 eq16470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6543
  have eq16490 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq6552 y
       have i₂ := eq16470
       grind)
    | exact superpose eq16470 eq6552
    | exact resolve eq6552 eq16470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6552 eq16470
  have eq16491 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16490
       have i₂ := eq43 x
       grind)
    | exact superpose eq43 eq16490
    | exact resolve eq16490 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq16490
  have eq16492 : (M.op x y) = (k x y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16488
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16488
    | exact resolve eq16488 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq16488
  have eq16501 : (k (σ x) (σ y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16491
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16491
    | exact resolve eq16491 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq16491
  have eq16508 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16501
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16501
    | exact resolve eq16501 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq16501
  have eq16511 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq16508
    | exact resolve eq16508 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq16508
  have eq16571 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq16511 eq101
    | exact resolve eq101 eq16511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq16511
  have eq16576 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq16492 eq16571
    | exact resolve eq16571 eq16492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16492 eq16571
  have eq16577 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq16576
  have eq16607 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16577 eq15
    | exact resolve eq15 eq16577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16577
  have eq16650 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq16607
    | exact resolve eq16607 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq16607
  have eq16651 : False := by grind
  exact eq16651

/-- `x □ y = if m(X,X) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,Y) = X then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_y_pxy_pyx_pyy_x_pyx_pxy_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = M.op b a ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = b ∨ M.op a b = M.op b a ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    grind
  have eq34 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24
    | exact resolve eq24 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X1)
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq43 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq43
    | (have j0 := eq43 (σ X0) (σ X1)
       grind)
    | exact resolve eq43 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq76 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq75 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq77 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq76 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq78 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq34
  have eq79 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq78 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq84 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq79 (τ X0)
       grind)
    | exact superpose eq79 eq35
    | exact resolve eq35 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq86 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq24 (σ X0) X0
       have i₂ := eq79 (σ X0)
       grind)
    | exact superpose eq79 eq24
    | exact resolve eq24 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq87 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq20 X0 (τ X0)
       have i₂ := eq79 (τ X0)
       grind)
    | exact superpose eq79 eq20
    | exact resolve eq20 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq87 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq87
    | exact resolve eq87 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq89 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq86 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq86
    | exact resolve eq86 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq91 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq84
    | exact resolve eq84 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq96 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq88 X0
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq88
    | exact resolve eq88 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq97 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq89 X0
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq89
    | exact resolve eq89 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq89
  have eq102 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq20 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq77 (τ X0)
       grind)
    | exact superpose eq77 eq20
    | (have j1 := eq77 (τ X0)
       grind)
    | exact resolve eq20 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq104 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq96 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq96
    | exact resolve eq96 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq121 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq57 x y
       grind)
    | exact superpose eq57 eq16
    | (have j1 := eq57 x y
       grind)
    | exact resolve eq16 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq339 : ∀ X0 : G, (k X0 (σ (τ (M.op X0 X0)))) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq25
    | exact resolve eq25 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq340 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq339 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq339
    | exact resolve eq339 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq341 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    grind
  clear eq340
  have eq347 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (τ (M.op (σ X0) (σ X0))) X0)) := by
    intro X0
    first
    | (have i₁ := eq341 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq341
    | exact resolve eq341 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq372 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq347 X0
       have i₂ := eq97 X0
       grind)
    | exact superpose eq97 eq347
    | exact resolve eq347 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq377 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq372 X0
       have i₂ := eq104 X0
       grind)
    | exact superpose eq104 eq372
    | exact resolve eq372 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq551 : (σ x) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq121
       have i₂ := eq104 y
       grind)
    | exact superpose eq104 eq121
    | exact resolve eq121 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq552 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq551
       have i₂ := eq104 x
       grind)
    | exact superpose eq104 eq551
    | exact resolve eq551 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq554 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq552
       have i₂ := eq43 x y
       grind)
    | exact superpose eq43 eq552
    | (have j1 := eq43 x y
       grind)
    | exact resolve eq552 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq552
  have eq555 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq554
  have eq559 : ∀ X0 : G, (k (σ (τ (M.op X0 X0))) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq102
    | (have j0 := eq102 X0
       grind)
    | exact resolve eq102 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq560 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq559 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq559
    | (have j0 := eq559 X0
       grind)
    | exact resolve eq559 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq561 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (k (M.op X0 X0) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq560 X0
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq560
    | (have j0 := eq560 X0
       grind)
    | exact resolve eq560 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq562 : ∀ X0 : G, (τ X0) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (k (M.op X0 X0) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq561 X0
       have i₂ := eq91 (M.op X0 X0)
       grind)
    | exact superpose eq91 eq561
    | (have j0 := eq561 X0
       grind)
    | exact resolve eq561 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq565 : ∀ X0 : G, (τ (σ X0)) = (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) ∨ (k (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (τ (σ X0)) (τ (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq562 (σ X0)
       have i₂ := eq104 X0
       grind)
    | exact superpose eq104 eq562
    | exact resolve eq562 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq590 : ∀ X0 : G, (τ (σ X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (τ (σ X0)) (τ (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq565 X0
       have i₂ := eq97 (M.op X0 X0)
       grind)
    | exact superpose eq97 eq565
    | (have j0 := eq565 X0
       grind)
    | exact resolve eq565 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq593 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (k (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (τ (σ X0)) (τ (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq590 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq590
    | (have j0 := eq590 X0
       grind)
    | exact resolve eq590 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq595 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (τ (σ X0)) (M.op X0 X0))) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq593 X0
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq593
    | (have j0 := eq593 X0
       grind)
    | exact resolve eq593 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq597 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (σ (M.op X0 (M.op X0 X0))) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq595 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq595
    | (have j0 := eq595 X0
       grind)
    | exact resolve eq595 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq599 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (σ (k (M.op X0 X0) X0)) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq597 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq597
    | (have j0 := eq597 X0
       grind)
    | exact resolve eq597 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq5454 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (σ (k (M.op X0 X0) X0)) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq599
  have eq16116 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) ∨ (σ (k (M.op (τ X0) (τ X0)) (τ X0))) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq20 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq5454 (τ X0)
       grind)
    | exact superpose eq5454 eq20
    | (have j1 := eq5454 (τ X0)
       grind)
    | exact resolve eq20 eq5454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5454
  have eq16169 : ∀ X0 : G, (k (σ (τ (M.op X0 X0))) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) ∨ (σ (k (M.op (τ X0) (τ X0)) (τ X0))) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq16116 X0
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq16116
    | (have j0 := eq16116 X0
       grind)
    | exact resolve eq16116 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16116
  have eq16219 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) ∨ (σ (k (M.op (τ X0) (τ X0)) (τ X0))) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq16169 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq16169
    | (have j0 := eq16169 X0
       grind)
    | exact resolve eq16169 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16169
  have eq16269 : ∀ X0 : G, (σ (M.op (τ X0) (τ (M.op X0 X0)))) = (σ (k (τ (M.op X0 X0)) (τ X0))) ∨ (k (M.op X0 X0) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq16219 X0
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq16219
    | (have j0 := eq16219 X0
       grind)
    | exact resolve eq16219 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq16219
  have eq16318 : ∀ X0 : G, (k (M.op X0 X0) (σ (τ X0))) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) ∨ (k (M.op X0 X0) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq16269 X0
       have i₂ := eq19 (M.op X0 X0) (τ X0)
       grind)
    | exact superpose eq19 eq16269
    | (have j0 := eq16269 X0
       grind)
    | exact resolve eq16269 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq16269
  have eq16374 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) ∨ (k (M.op X0 X0) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq16318 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16318
    | (have j0 := eq16318 X0
       grind)
    | exact resolve eq16318 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16318
  have eq16375 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq16374 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16374
  have eq16658 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (τ (σ X0)) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq16375 (σ X0)
       have i₂ := eq97 X0
       grind)
    | exact superpose eq97 eq16375
    | exact resolve eq16375 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq16375
  have eq16751 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq16658 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq16658
    | exact resolve eq16658 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16658
  have eq16774 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq16751 X0
       have i₂ := eq104 X0
       grind)
    | exact superpose eq104 eq16751
    | exact resolve eq16751 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16751
  have eq16790 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq16774 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq16774
    | exact resolve eq16774 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16774
  have eq17063 : ∀ X0 : G, (k (M.op X0 X0) X0) = (τ (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq9 (k (M.op X0 X0) X0)
       have i₂ := eq16790 X0
       grind)
    | exact superpose eq16790 eq9
    | exact resolve eq9 eq16790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17169 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq17063 X0
       have i₂ := eq9 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq9 eq17063
    | exact resolve eq17063 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17063
  have eq17450 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq17169 (σ X0)
       have i₂ := eq104 X0
       grind)
    | exact superpose eq104 eq17169
    | exact resolve eq17169 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq17169
  have eq17589 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq17450 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq17450
    | exact resolve eq17450 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17450
  have eq17639 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq17589 X0
       have i₂ := eq16790 X0
       grind)
    | exact superpose eq16790 eq17589
    | exact resolve eq17589 eq16790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16790 eq17589
  have eq19405 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq17639 x
       have i₂ := eq555
       grind)
    | exact superpose eq555 eq17639
    | exact resolve eq17639 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq19445 : x = (M.op y y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq19405
       have r₂ := eq16
       grind)
    | exact resolve eq19405 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19405
  have eq23692 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq377 y
       have i₂ := eq19445
       grind)
    | exact superpose eq19445 eq377
    | exact resolve eq377 eq19445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19445
  have eq23740 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq23692
       have r₂ := eq16
       grind)
    | exact resolve eq23692 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23692
  have eq24271 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq23740
       grind)
    | exact superpose eq23740 eq9
    | exact resolve eq9 eq23740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23740
  have eq24383 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq24271
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq24271
    | exact resolve eq24271 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24271
  have eq24431 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq17639 x
       have i₂ := eq24383
       grind)
    | exact superpose eq24383 eq17639
    | exact resolve eq17639 eq24383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17639 eq24383
  have eq24448 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq24431
       have r₂ := eq16
       grind)
    | exact resolve eq24431 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24431
  have eq24467 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq24448
       grind)
    | exact superpose eq24448 eq9
    | exact resolve eq9 eq24448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24448
  have eq24579 : x = (M.op y y) := by
    first
    | (have i₁ := eq24467
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq24467
    | exact resolve eq24467 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24467
  have eq24993 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq377 y
       have i₂ := eq24579
       grind)
    | exact superpose eq24579 eq377
    | exact resolve eq377 eq24579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377 eq24579
  have eq25036 : False := by grind
  exact eq25036

/-- `x □ y = if m(X,X) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(Y,X) else if m(Y,Y) = X then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_y_pxy_pyx_pyy_x_pyx_pyx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = M.op b a ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = b ∨ M.op a b = M.op b a ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    grind
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24
    | exact resolve eq24 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq24
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq24 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X1 : G, (M.op (M.op X1 X1) (M.op X1 X1)) = X1 ∨ (M.op X1 (M.op X1 X1)) = (k (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq75 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  clear eq62
  have eq80 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq75 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq83 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq20 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq80 (τ X0)
       grind)
    | exact superpose eq80 eq20
    | exact resolve eq20 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq34
  have eq105 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq103 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq114 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq31 X0 (σ X0)
       have i₂ := eq105 (σ X0)
       grind)
    | exact superpose eq105 eq31
    | exact resolve eq31 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq105 (τ X0)
       grind)
    | exact superpose eq105 eq35
    | exact resolve eq35 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq105 (τ X0)
       grind)
    | exact superpose eq105 eq19
    | exact resolve eq19 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq117 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq116 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq116
    | exact resolve eq116 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq118 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq115 X0
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq115
    | exact resolve eq115 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq119 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq114 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq114
    | exact resolve eq114 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq126 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq117 X0
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq117
    | exact resolve eq117 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq127 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq119 X0
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq119
    | exact resolve eq119 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq119
  have eq131 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq126 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq126
    | exact resolve eq126 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq335 : ∀ X0 : G, (k X0 (σ (τ (M.op X0 X0)))) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq118 X0
       grind)
    | exact superpose eq118 eq25
    | exact resolve eq25 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq336 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq335 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq335
    | exact resolve eq335 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq337 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    grind
  clear eq336
  have eq343 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (τ (M.op (σ X0) (σ X0))) X0)) := by
    intro X0
    first
    | (have i₁ := eq337 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq337
    | exact resolve eq337 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq367 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq343 X0
       have i₂ := eq127 X0
       grind)
    | exact superpose eq127 eq343
    | exact resolve eq343 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq371 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq367 X0
       have i₂ := eq131 X0
       grind)
    | exact superpose eq131 eq367
    | exact resolve eq367 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq375 : ∀ X0 : G, (σ (M.op (τ X0) (τ (M.op X0 X0)))) = (k (σ (τ (M.op X0 X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq118 X0
       grind)
    | exact superpose eq118 eq83
    | exact resolve eq83 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq118
  have eq376 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq375 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq375
    | exact resolve eq375 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq377 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq376 X0
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq376
    | exact resolve eq376 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq376
  have eq378 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X0 (τ (M.op (σ X0) (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq377 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq377
    | exact resolve eq377 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq409 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq378 X0
       have i₂ := eq127 X0
       grind)
    | exact superpose eq127 eq378
    | exact resolve eq378 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq378
  have eq413 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq409 X0
       have i₂ := eq131 X0
       grind)
    | exact superpose eq131 eq409
    | exact resolve eq409 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq3710 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ (M.op X1 X1)) = X0 ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq131 X1
       grind)
    | exact superpose eq131 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq3796 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (σ (M.op (τ X0) (τ X0))) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3710 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3710
    | (have j0 := eq3710 X1 (τ X0)
       grind)
    | exact resolve eq3710 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3710
  have eq3883 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (σ (M.op (τ X0) (τ X0))) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3796 X0 X1
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq3796
    | (have j0 := eq3796 X0 X1
       grind)
    | exact resolve eq3796 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3796
  have eq3893 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3883 X0 X1
       have i₂ := eq126 X0
       grind)
    | exact superpose eq126 eq3883
    | (have j0 := eq3883 X0 X1
       grind)
    | exact resolve eq3883 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3883
  have eq18491 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3893 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3893
    | (have j0 := eq3893 (σ X1) (σ X0)
       grind)
    | exact resolve eq3893 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3893
  have eq18767 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18491 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq18491
    | (have j0 := eq18491 X0 X1
       grind)
    | exact resolve eq18491 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18491
  have eq18789 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18767 X0 X1
       have i₂ := eq131 X1
       grind)
    | exact superpose eq131 eq18767
    | (have j0 := eq18767 X0 X1
       grind)
    | exact resolve eq18767 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18767
  have eq18790 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18789 X0 X1
       have i₂ := eq131 X0
       grind)
    | exact superpose eq131 eq18789
    | (have j0 := eq18789 X0 X1
       grind)
    | exact resolve eq18789 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18789
  have eq550398 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq18790 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq18790 X0 X1
       grind)
    | exact superpose eq18790 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq18790 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq18790 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq18790 X0 X1
       grind)
    | exact resolve eq12 eq18790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18790
  have eq550401 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq550398 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550398
  have eq550454 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq550401 X0 X1
       have i₂ := eq131 X0
       grind)
    | exact superpose eq131 eq550401
    | (have j0 := eq550401 X0 X1
       grind)
    | exact resolve eq550401 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550401
  have eq550455 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq550454 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550454
  have eq550509 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq550455 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq550455
    | (have j0 := eq550455 X0 X1
       grind)
    | exact resolve eq550455 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550455
  have eq980401 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 ∨ (σ X1) = (σ (M.op (τ X0) (τ X0))) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq550509 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq550509
    | (have j0 := eq550509 (τ X0) X1
       grind)
    | exact resolve eq550509 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550509
  have eq981456 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 ∨ (σ X1) = (σ (M.op (τ X0) (τ X0))) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq980401 X0 X1
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq980401
    | (have j0 := eq980401 X0 X1
       grind)
    | exact resolve eq980401 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq980401
  have eq981746 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) ∨ (σ (M.op X1 X1)) = X0 ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq981456 X0 X1
       have i₂ := eq126 X0
       grind)
    | exact superpose eq126 eq981456
    | (have j0 := eq981456 X0 X1
       grind)
    | exact resolve eq981456 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981456
  have eq982636 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) ∨ (σ (M.op X0 X0)) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq981746 X1 X0
       grind)
    | exact superpose eq981746 eq31
    | (have j1 := eq981746 X1 X0
       grind)
    | exact resolve eq31 eq981746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq982904 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) X1
       have i₂ := eq981746 (σ X1) X0
       grind)
    | exact superpose eq981746 eq24
    | (have j1 := eq981746 (σ X1) X0
       grind)
    | exact resolve eq24 eq981746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq981746
  have eq983420 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq982636 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982636
  have eq983722 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq982904 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq982904
    | (have j0 := eq982904 X0 X1
       grind)
    | exact resolve eq982904 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982904
  have eq983999 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq983722 X0 X1
       have i₂ := eq131 X1
       grind)
    | exact superpose eq131 eq983722
    | (have j0 := eq983722 X0 X1
       grind)
    | exact resolve eq983722 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq983722
  have eq984158 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq983999 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq983999
    | (have j0 := eq983999 X0 X1
       grind)
    | exact resolve eq983999 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983999
  have eq984159 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq984158 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984158
  have eq984256 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq983420 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq983420
    | (have j0 := eq983420 (τ X0) X1
       grind)
    | exact resolve eq983420 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983420
  have eq985948 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq984256 X0 X1
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq984256
    | (have j0 := eq984256 X0 X1
       grind)
    | exact resolve eq984256 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq984256
  have eq986150 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq985948 X0 X1
       have i₂ := eq126 X0
       grind)
    | exact superpose eq126 eq985948
    | (have j0 := eq985948 X0 X1
       grind)
    | exact resolve eq985948 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq985948
  have eq986849 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq986150 X0 X1
       grind)
    | exact superpose eq986150 eq10
    | (have j1 := eq986150 X0 X1
       grind)
    | exact resolve eq10 eq986150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986150
  have eq987925 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq986849 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq986849
    | (have j0 := eq986849 X0 X1
       grind)
    | exact resolve eq986849 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986849
  have eq1067043 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ X1))
       have i₂ := eq984159 X0 X1
       grind)
    | exact superpose eq984159 eq10
    | (have j1 := eq984159 X0 X1
       grind)
    | exact resolve eq10 eq984159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984159
  have eq1072047 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1067043 x y
       grind)
    | exact superpose eq1067043 eq16
    | (have j1 := eq1067043 x y
       grind)
    | exact resolve eq16 eq1067043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067043
  have eq1074227 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1072047
       have i₂ := eq987925 x y
       grind)
    | exact superpose eq987925 eq1072047
    | (have j1 := eq987925 x y
       grind)
    | exact resolve eq1072047 eq987925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987925 eq1072047
  have eq1074244 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq1074227
  have eq1084343 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq413 x
       have i₂ := eq1074244
       grind)
    | exact superpose eq1074244 eq413
    | exact resolve eq413 eq1074244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074244
  have eq1084455 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq1084343
       have r₂ := eq16
       grind)
    | exact resolve eq1084343 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084343
  have eq1084469 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq371 y
       have i₂ := eq1084455
       grind)
    | exact superpose eq1084455 eq371
    | exact resolve eq371 eq1084455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084455
  have eq1084583 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1084469
       have r₂ := eq16
       grind)
    | exact resolve eq1084469 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084469
  have eq1084617 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq1084583
       grind)
    | exact superpose eq1084583 eq9
    | exact resolve eq9 eq1084583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084583
  have eq1085233 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1084617
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1084617
    | exact resolve eq1084617 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084617
  have eq1085247 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq413 x
       have i₂ := eq1085233
       grind)
    | exact superpose eq1085233 eq413
    | exact resolve eq413 eq1085233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413 eq1085233
  have eq1085358 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1085247
       have r₂ := eq16
       grind)
    | exact resolve eq1085247 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085247
  have eq1085392 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq1085358
       grind)
    | exact superpose eq1085358 eq9
    | exact resolve eq9 eq1085358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085358
  have eq1086008 : x = (M.op y y) := by
    first
    | (have i₁ := eq1085392
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq1085392
    | exact resolve eq1085392 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085392
  have eq1086019 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq371 y
       have i₂ := eq1086008
       grind)
    | exact superpose eq1086008 eq371
    | exact resolve eq371 eq1086008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371 eq1086008
  have eq1086133 : False := by grind
  exact eq1086133
