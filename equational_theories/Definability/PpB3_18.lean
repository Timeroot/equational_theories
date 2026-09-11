import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2702`: `x = ((y ◇ x) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_y_pyx_Equation2702 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2702 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2702.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X0 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq101 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op X0 X3)) X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op x X0) (M.op X0 x)) X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = (M.op (M.op (M.op (M.op X1 X0) (M.op X0 X2)) X0) (M.op (M.op X1 X0) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq103 (M.op (M.op X1 X0) (M.op X0 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq103
    | exact resolve eq103 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq109 X0 X1 X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq109
    | exact resolve eq109 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq116 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 (M.op X0 X1)) = X0 ∨ (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 (M.op X0 X1))
       have i₂ := eq103 X0 X1
       grind)
    | exact superpose eq103 eq13
    | (have j0 := eq13 (M.op X0 (M.op X0 X1)) X0
       grind)
    | (have r₁ := eq13 X0 (M.op X0 (M.op X0 x))
       have r₂ := eq103 X0 x
       grind)
    | exact resolve eq13 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) ∨ (M.op X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq116 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq167 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq167 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq167
    | (have j0 := eq167 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq167 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18385 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq530 x y
       grind)
    | exact superpose eq530 eq16
    | (have j1 := eq530 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq530 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq530 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq530 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq18462 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq18385
  have eq18509 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq18462
       grind)
    | exact superpose eq18462 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq18462
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq18462
       grind)
    | exact resolve eq13 eq18462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18517 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq117 (σ x) (σ y)
       have i₂ := eq18462
       grind)
    | exact superpose eq18462 eq117
    | exact resolve eq117 eq18462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18543 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq18509
  have eq18544 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq18543
  have eq18553 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq18462 eq18517
    | exact resolve eq18517 eq18462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18517
  have eq18557 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18544
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq18544
    | exact resolve eq18544 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18544
  have eq18566 : (σ y) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18553
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq18553
    | exact resolve eq18553 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18553
  have eq18567 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq14 eq18557
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq18557 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18557
  have eq18571 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq18462 eq18566
    | exact resolve eq18566 eq18462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18566
  have eq18572 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq18571
  have eq18576 : (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq18567
       grind)
    | exact superpose eq18567 eq10
    | exact resolve eq10 eq18567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18567
  have eq18758 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18576
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq18576
    | exact resolve eq18576 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18576
  have eq18761 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18758
       grind)
    | exact superpose eq18758 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq18758
       grind)
    | exact resolve eq13 eq18758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18762 : x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq103 x y
       have i₂ := eq18758
       grind)
    | exact superpose eq18758 eq103
    | exact resolve eq103 eq18758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18769 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq117 x y
       have i₂ := eq18758
       grind)
    | exact superpose eq18758 eq117
    | exact resolve eq117 eq18758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq18797 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18769
  have eq18798 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq18761
  have eq18799 : x = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq18798
  have eq18807 : y = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq18758 eq18797
    | exact resolve eq18797 eq18758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18797
  have eq18810 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq18758 eq18762
    | exact resolve eq18762 eq18758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18762
  have eq18813 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq167 y x
       have i₂ := eq18799
       grind)
    | exact superpose eq18799 eq167
    | (have j0 := eq167 y x
       grind)
    | exact resolve eq167 eq18799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18799
  have eq18819 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq18813
  have eq18822 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq18462 eq18819
    | exact resolve eq18819 eq18462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18462 eq18819
  have eq18823 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18822
  have eq18890 : (τ (σ y)) = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq18572
       grind)
    | exact superpose eq18572 eq10
    | exact resolve eq10 eq18572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18572
  have eq19076 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18890
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq18890
    | exact resolve eq18890 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18890
  have eq19081 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq18807 eq19076
    | exact resolve eq19076 eq18807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18807 eq19076
  have eq19082 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq19081
  have eq19084 : y = (M.op y x) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq19082
       grind)
    | exact superpose eq19082 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq19082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19085 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq167 x y
       have i₂ := eq19082
       grind)
    | exact superpose eq19082 eq167
    | (have j0 := eq167 x y
       grind)
    | exact resolve eq167 eq19082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167 eq19082
  have eq19091 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq19085
  have eq19092 : y = (M.op y x) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq19084
  have eq19095 : ∀ X0 : G, x = (M.op (M.op y (M.op x X0)) x) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq19092
       grind)
    | exact superpose eq19092 eq9
    | exact resolve eq9 eq19092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19104 : ∀ X0 : G, (M.op (M.op X0 y) y) = (M.op y (M.op (M.op X0 y) y)) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq114 y x x
       have i₂ := eq19092
       grind)
    | exact superpose eq19092 eq114
    | exact resolve eq114 eq19092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq20210 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq18823
       grind)
    | exact superpose eq18823 eq16
    | exact resolve eq16 eq18823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18823
  have eq20593 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq20210
       have i₂ := eq18758
       grind)
    | exact superpose eq18758 eq20210
    | exact resolve eq20210 eq18758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18758 eq20210
  have eq20594 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq20593
  have eq20595 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq20594
  have eq20606 : (σ x) = (M.op (M.op (σ (M.op x x)) (σ x)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq101 x (σ y)
       have i₂ := eq20595
       grind)
    | exact superpose eq20595 eq101
    | exact resolve eq101 eq20595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq20638 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq103 (σ x) (σ y)
       have i₂ := eq20595
       grind)
    | exact superpose eq20595 eq103
    | exact resolve eq103 eq20595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20689 : (σ x) = (M.op (σ (M.op x x)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20638
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq20638
    | exact resolve eq20638 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20638
  have eq49162 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20689 eq20606
    | exact resolve eq20606 eq20689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20606 eq20689
  have eq49163 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq49162
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq49162
    | exact resolve eq49162 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49162
  have eq49221 : (M.op x x) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq49163
       grind)
    | exact superpose eq49163 eq10
    | exact resolve eq10 eq49163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49163
  have eq49454 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq49221
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq49221
    | exact resolve eq49221 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49221
  have eq49515 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq19104 x
       have i₂ := eq49454
       grind)
    | exact superpose eq49454 eq19104
    | exact resolve eq19104 eq49454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19104
  have eq49572 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq49515
  have eq49581 : x = (M.op y x) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq18810 eq49572
    | exact resolve eq49572 eq18810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18810 eq49572
  have eq49582 : x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq49581
  have eq49604 : y = (M.op (M.op y x) y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq103 y x
       have i₂ := eq49582
       grind)
    | exact superpose eq49582 eq103
    | exact resolve eq103 eq49582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49671 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq49582 eq49604
    | exact resolve eq49604 eq49582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49582 eq49604
  have eq49673 : x = y ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq49454 eq49671
    | exact resolve eq49671 eq49454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49454 eq49671
  have eq49674 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq49673
  have eq49680 : x = (M.op (M.op y x) x) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq19095 x
       have i₂ := eq49674
       grind)
    | exact superpose eq49674 eq19095
    | exact resolve eq19095 eq49674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19095 eq49674
  have eq49871 : x = (M.op (M.op y x) x) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq49680
  have eq49941 : x = (M.op y x) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq19092 eq49871
    | exact resolve eq49871 eq19092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19092 eq49871
  have eq49942 : x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq49941
  have eq50066 : y = (M.op (M.op y x) y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq103 y x
       have i₂ := eq49942
       grind)
    | exact superpose eq49942 eq103
    | exact resolve eq103 eq49942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50132 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq49942 eq50066
    | exact resolve eq50066 eq49942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49942 eq50066
  have eq50143 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq50132 eq20595
    | exact resolve eq20595 eq50132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20595 eq50132
  have eq50195 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq50143
  have eq50285 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ y) X0)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) (σ x) X0
       have i₂ := eq50195
       grind)
    | exact superpose eq50195 eq9
    | exact resolve eq9 eq50195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51324 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq50285 (σ x)
       have i₂ := eq19091
       grind)
    | exact superpose eq19091 eq50285
    | exact resolve eq50285 eq19091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19091 eq50285
  have eq51424 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq51324
  have eq51446 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq50195 eq51424
    | exact resolve eq51424 eq50195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51424
  have eq51450 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq50195 eq51446
    | exact resolve eq51446 eq50195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51446
  have eq51451 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq51450
  have eq51515 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq103 (σ y) (σ x)
       have i₂ := eq51451
       grind)
    | exact superpose eq51451 eq103
    | exact resolve eq103 eq51451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq51579 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq51451 eq51515
    | exact resolve eq51515 eq51451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51451 eq51515
  have eq51594 : (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq50195 eq51579
    | exact resolve eq51579 eq50195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50195 eq51579
  have eq51595 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq51594
  have eq51608 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq51595
       grind)
    | exact superpose eq51595 eq10
    | exact resolve eq10 eq51595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51595
  have eq51833 : x = y ∨ x = y := by
    first
    | (have i₁ := eq51608
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq51608
    | exact resolve eq51608 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51608
  have eq51834 : x = y := by grind
  clear eq51833
  have eq51837 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq51834
       grind)
    | exact superpose eq51834 eq16
    | exact resolve eq16 eq51834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51834
  have eq51838 : False := by grind
  exact eq51838

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyx_pyx_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq23 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq23 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq23 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq23 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq41 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq42 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq39 (k X0 X0) X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq39 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq34 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq34 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq40 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq40 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq40 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq41 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq41 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq41 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq48
  have eq57 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq42 X1 X0
       grind)
    | (have r₁ := eq53 X1 X0
       have r₂ := eq42 X0 X1
       grind)
    | (have r₁ := eq53 X0 (M.op X1 X1)
       have r₂ := eq42 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq53 X1 X1
       have r₂ := eq42 (k X1 X1) X1
       grind)
    | exact resolve eq53 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq53
  have eq59 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       have j1 := eq55 X0 X1
       grind)
    | (have r₁ := eq56 X0 X1
       have r₂ := eq55 X0 X1
       grind)
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq56
  have eq106 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq110 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq106 X0 X1
       have j1 := eq59 X1 X0
       grind)
    | (have r₁ := eq106 X1 X0
       have r₂ := eq59 X0 X1
       grind)
    | (have r₁ := eq106 X0 X0
       have r₂ := eq59 X0 X0
       grind)
    | exact resolve eq106 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq106
  have eq295 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq110 (σ X1) (σ X0)
       grind)
    | exact superpose eq110 eq15
    | exact resolve eq15 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq295 X0 X1
       have i₂ := eq110 X1 X0
       grind)
    | exact superpose eq110 eq295
    | exact resolve eq295 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq295
  have eq304 : False := by grind
  exact eq304

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_x_pxx_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X0 X0) X0 X2
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq61
    | exact resolve eq61 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq90 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq76
    | exact resolve eq76 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq471 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq73 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq2787 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq170 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq170
    | (have j0 := eq170 X1 X1
       have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq170 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2788 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) ∨ (σ (σ X1)) = (M.op (σ (σ X1)) (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq170 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq170
    | (have j0 := eq170 (σ X0) (σ X0)
       grind)
    | exact resolve eq170 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16263 : ∀ X0 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq2788 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2788
  have eq16265 : ∀ X0 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq16263 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16263
  have eq16328 : ∀ X0 : G, (σ (σ (τ X0))) ≠ (σ (k (σ (τ X0)) X0)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq16265 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq16265
    | (have j0 := eq16265 (τ X0)
       grind)
    | exact resolve eq16265 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16265
  have eq16340 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq16328 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16328
    | (have j0 := eq16328 X0
       grind)
    | exact resolve eq16328 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16328
  have eq16347 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16340 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16340
    | (have j0 := eq16340 X0
       grind)
    | exact resolve eq16340 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16340
  have eq16355 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq16347 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq16347
    | (have j0 := eq16347 (τ X0)
       grind)
    | exact resolve eq16347 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq16347
  have eq16367 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq16355 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16355
    | (have j0 := eq16355 X0
       grind)
    | exact resolve eq16355 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16355
  have eq16374 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16367 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16367
    | (have j0 := eq16367 X0
       grind)
    | exact resolve eq16367 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16367
  have eq16575 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2787 x y
       grind)
    | exact superpose eq2787 eq16
    | (have j1 := eq2787 y y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2787 x y
       grind)
    | exact resolve eq16 eq2787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2787
  have eq16733 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq16575
  have eq30236 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ y)
       have i₂ := eq16733
       grind)
    | exact superpose eq16733 eq12
    | (have r₁ := eq12 (σ y) (σ y)
       have r₂ := eq16733
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq16733
       grind)
    | (have r₁ := eq12 y y
       have r₂ := eq16733
       grind)
    | exact resolve eq12 eq16733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16733
  have eq30342 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq30236
  have eq30384 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30342
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq30342
    | exact resolve eq30342 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30342
  have eq43697 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90 (σ x) (σ y)
       have i₂ := eq30384
       grind)
    | exact superpose eq30384 eq90
    | exact resolve eq90 eq30384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30384
  have eq48263 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ x)
       have i₂ := eq43697
       grind)
    | exact superpose eq43697 eq12
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq43697
       grind)
    | (have r₁ := eq12 y y
       have r₂ := eq43697
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq43697
       grind)
    | exact resolve eq12 eq43697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43697
  have eq48401 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq48263
  have eq48449 : (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq48401
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq48401
    | exact resolve eq48401 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48401
  have eq48503 : (k y y) = (τ (σ y)) ∨ (σ x) = (σ (k x x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq48449
       grind)
    | exact superpose eq48449 eq10
    | exact resolve eq10 eq48449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48449
  have eq48659 : y = (k y y) ∨ (σ x) = (σ (k x x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq48503
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq48503
    | exact resolve eq48503 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48503
  have eq48668 : (σ x) = (σ (k x x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq16374 y
       grind)
    | (have r₁ := eq48659
       have r₂ := eq16374 y
       grind)
    | exact resolve eq48659 eq16374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16374 eq48659
  have eq48685 : (τ (σ x)) = (k x x) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq48668
       grind)
    | exact superpose eq48668 eq10
    | exact resolve eq10 eq48668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48668
  have eq48841 : y = (M.op y y) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq48685
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq48685
    | exact resolve eq48685 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48685
  have eq48857 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (k x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq76 y X0
       have i₂ := eq48841
       grind)
    | exact superpose eq48841 eq76
    | exact resolve eq76 eq48841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48952 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (k x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq471 y y x
       have i₂ := eq48841
       grind)
    | exact superpose eq48841 eq471
    | exact resolve eq471 eq48841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48841
  have eq49067 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (k x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq48952 X0
       have i₂ := eq90 y X0
       grind)
    | exact superpose eq90 eq48952
    | exact resolve eq48952 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48952
  have eq50911 : ∀ X0 : G, x = (k x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq49067 eq48857
    | exact resolve eq48857 eq49067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48857 eq49067
  have eq50953 : ∀ X0 : G, x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 x x
       have i₂ := eq50911 X0
       grind)
    | exact superpose eq50911 eq14
    | (have j0 := eq14 x x
       have j1 := eq50911 X0
       grind)
    | exact resolve eq14 eq50911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50911
  have eq50954 : ∀ X0 : G, x = (M.op x y) ∨ (M.op y X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq50953 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50953
  have eq52585 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq90 x y
       have i₂ := eq50954 X0
       grind)
    | exact superpose eq50954 eq90
    | (have j1 := eq50954 X0
       grind)
    | exact resolve eq90 eq50954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50954
  have eq52700 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq52585 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52585
  have eq52865 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq76 x X0
       have i₂ := eq52700 X1
       grind)
    | exact superpose eq52700 eq76
    | (have j1 := eq52700 X1
       grind)
    | exact resolve eq76 eq52700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq52960 : ∀ X0 X1 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq471 x x x
       have i₂ := eq52700 X0
       grind)
    | exact superpose eq52700 eq471
    | (have j1 := eq52700 X1
       grind)
    | exact resolve eq471 eq52700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52700
  have eq53078 : ∀ X0 X1 : G, x = (M.op (M.op x X0) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52960 X0 X1
       have i₂ := eq90 x X0
       grind)
    | exact superpose eq90 eq52960
    | (have j0 := eq52960 X0 X1
       grind)
    | exact resolve eq52960 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq52960
  have eq55284 : ∀ X0 X1 : G, (M.op y X1) = X1 ∨ (M.op x X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq53078 eq52865
    | (have j0 := eq52865 X0 X1
       have j1 := eq53078 X0 X1
       grind)
    | exact resolve eq52865 eq53078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52865
  have eq55285 : ∀ X0 X1 : G, x = (M.op X0 x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq55284 eq53078
    | (have j0 := eq53078 X0 X1
       have j1 := eq55284 X0 X1
       grind)
    | exact resolve eq53078 eq55284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53078
  have eq55293 : ∀ X0 : G, y ≠ y ∨ y = (k y y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq75 y
       have i₂ := eq55284 X0 y
       grind)
    | exact superpose eq55284 eq75
    | (have j1 := eq55284 X0 x
       grind)
    | (have r₁ := eq75 y
       have r₂ := eq55284 X0 y
       grind)
    | (have r₁ := eq75 x
       have r₂ := eq55284 x x
       grind)
    | exact resolve eq75 eq55284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55390 : ∀ X0 X1 X2 : G, (M.op y X1) = (M.op (M.op (M.op y X1) X0) (M.op y X1)) ∨ (M.op x X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq471 y X1 X0
       have i₂ := eq55284 X2 X0
       grind)
    | exact superpose eq55284 eq471
    | (have j1 := eq55284 X2 X1
       grind)
    | exact resolve eq471 eq55284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq55520 : ∀ X0 X1 : G, y = (M.op (M.op (M.op y y) X0) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq77 y X0
       have i₂ := eq55284 X1 (M.op (M.op y y) X0)
       grind)
    | exact superpose eq55284 eq77
    | (have j1 := eq55284 X1 X1
       grind)
    | exact resolve eq77 eq55284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55690 : ∀ X0 : G, y = (k y y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq55293 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55293
  have eq55800 : ∀ X0 X1 : G, y = (M.op (M.op y X0) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq55284 eq55520
    | (have j0 := eq55520 X0 X1
       have j1 := eq55284 X1 X1
       grind)
    | exact resolve eq55520 eq55284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55520
  have eq55869 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X1) = X1 ∨ (M.op x X2) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq55284 eq55390
    | (have j0 := eq55390 X0 X1 X2
       have j1 := eq55284 X2 X1
       grind)
    | exact resolve eq55390 eq55284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55390
  have eq56008 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq55284 eq55800
    | (have j0 := eq55800 X0 X1
       have j1 := eq55284 X1 X1
       grind)
    | exact resolve eq55800 eq55284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55800
  have eq56900 : x ≠ x ∨ x = (M.op y x) := by
    first
    | (have j0 := eq55285 y x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55285
  have eq56901 : x = (M.op y x) := by grind
  clear eq56900
  have eq57742 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (M.op y X0) x) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 y x X1
       have i₂ := eq56901
       grind)
    | exact superpose eq56901 eq61
    | exact resolve eq61 eq56901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56901
  have eq58329 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq170 y y
       have i₂ := eq55690 X0
       grind)
    | exact superpose eq55690 eq170
    | (have j0 := eq170 y y
       have j1 := eq55690 X0
       grind)
    | exact resolve eq170 eq55690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55690
  have eq58332 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq58329 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58329
  have eq59111 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq56008 x y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59112 : y = (M.op x y) := by grind
  clear eq59111
  have eq59950 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq59112
       grind)
    | exact superpose eq59112 eq16
    | exact resolve eq16 eq59112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59958 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (M.op x X0) y) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 x y X1
       have i₂ := eq59112
       grind)
    | exact superpose eq59112 eq61
    | exact resolve eq61 eq59112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq59112
  have eq71767 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (σ y) (σ y)
       have i₂ := eq58332 X1
       grind)
    | exact superpose eq58332 eq9
    | (have j1 := eq58332 X1
       grind)
    | exact resolve eq9 eq58332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58332
  have eq71978 : ∀ X0 X1 : G, (M.op (σ y) X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq55869 eq71767
    | (have j0 := eq71767 X0 X1
       have j1 := eq55869 X0 X1 X1
       grind)
    | exact resolve eq71767 eq55869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55869 eq71767
  have eq73948 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (M.op x (σ y)) y) X0) (σ y)) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq59958 (σ y) X0
       have i₂ := eq71978 (M.op (M.op (M.op x (σ y)) y) X0) X1
       grind)
    | exact superpose eq71978 eq59958
    | (have j1 := eq71978 X0 X1
       grind)
    | exact resolve eq59958 eq71978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59958 eq71978
  have eq74151 : ∀ X0 X1 : G, (σ y) = (M.op (M.op y X0) (σ y)) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq56008 eq73948
    | (have j0 := eq73948 X0 X1
       have j1 := eq56008 X0 X1
       grind)
    | exact resolve eq73948 eq56008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56008 eq73948
  have eq74155 : ∀ X0 X1 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq55284 eq74151
    | (have j0 := eq74151 X0 X1
       have j1 := eq55284 X1 X1
       grind)
    | exact resolve eq74151 eq55284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55284 eq74151
  have eq77129 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq59950
       have i₂ := eq74155 (σ x) X0
       grind)
    | exact superpose eq74155 eq59950
    | (have j1 := eq74155 X0 X0
       grind)
    | (have r₁ := eq59950
       have r₂ := eq74155 (σ x) x
       grind)
    | exact resolve eq59950 eq74155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74155
  have eq77170 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq77129 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77129
  have eq77880 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq75 x
       have i₂ := eq77170 x
       grind)
    | exact superpose eq77170 eq75
    | (have r₁ := eq75 x
       have r₂ := eq77170 x
       grind)
    | exact resolve eq75 eq77170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq78122 : ∀ X0 : G, x = (M.op (M.op (M.op x x) X0) x) := by
    intro X0
    first
    | (have i₁ := eq77 x X0
       have i₂ := eq77170 (M.op (M.op x x) X0)
       grind)
    | exact superpose eq77170 eq77
    | exact resolve eq77 eq77170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq78308 : x = (k x x) := by grind
  clear eq77880
  have eq78428 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq78122 X0
       have i₂ := eq77170 x
       grind)
    | exact superpose eq77170 eq78122
    | exact resolve eq78122 eq77170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78122
  have eq78654 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq78428 X0
       have i₂ := eq77170 X0
       grind)
    | exact superpose eq77170 eq78428
    | exact resolve eq78428 eq77170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78428
  have eq79464 : x = (k x x) := by grind
  clear eq78308
  have eq79521 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq170 x x
       have i₂ := eq79464
       grind)
    | exact superpose eq79464 eq170
    | (have j0 := eq170 x x
       grind)
    | exact resolve eq170 eq79464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170 eq79464
  have eq79524 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq79521
  have eq80927 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq57742 X0 X1
       have i₂ := eq78654 (M.op y X0)
       grind)
    | exact superpose eq78654 eq57742
    | exact resolve eq57742 eq78654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57742 eq78654
  have eq82326 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq80927 X0 X1
       have i₂ := eq77170 X1
       grind)
    | exact superpose eq77170 eq80927
    | exact resolve eq80927 eq77170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77170 eq80927
  have eq84693 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ x)
       have i₂ := eq79524
       grind)
    | exact superpose eq79524 eq9
    | exact resolve eq9 eq79524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79524
  have eq84851 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq84693 X0
       have i₂ := eq82326 (σ x) X0
       grind)
    | exact superpose eq82326 eq84693
    | exact resolve eq84693 eq82326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82326 eq84693
  have eq84889 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq59950
       have i₂ := eq84851 (σ y)
       grind)
    | exact superpose eq84851 eq59950
    | (have r₁ := eq59950
       have r₂ := eq84851 (σ y)
       grind)
    | exact resolve eq59950 eq84851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59950 eq84851
  have eq85110 : False := by grind
  exact eq85110

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_x_pxy_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
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
  clear eq17
  have eq26 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
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
  clear eq22
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) ≠ X0 ∨ (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq51 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq51
    | exact resolve eq51 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X1 (M.op X0 X0) X0 X2
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq51
    | exact resolve eq51 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq75 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq76
    | exact resolve eq76 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k (M.op X0 X1) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2) X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 (M.op X0 X0) X0 X2
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq52
    | exact resolve eq52 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq200 y x
       grind)
    | exact superpose eq200 eq16
    | (have j1 := eq200 y y
       grind)
    | exact resolve eq16 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq363 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ X1) X2) (σ (k X0 X1))) X2) = X2 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X1) (σ X0)
       have i₂ := eq200 X0 X1
       grind)
    | exact superpose eq200 eq9
    | (have j1 := eq200 X0 X0
       grind)
    | exact resolve eq9 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq364 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq200 X0 X1
       grind)
    | exact superpose eq200 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq200 X0 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq200 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq200 X0 X1
       grind)
    | exact resolve eq12 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq377 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq68 (σ X0)
       have i₂ := eq200 X0 X0
       grind)
    | exact superpose eq200 eq68
    | (have j1 := eq200 X0 X0
       grind)
    | exact resolve eq68 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq200 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq378 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq381 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq377 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq385 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq364 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq364 X0 X1
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq364 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq364 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq392 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq385 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq385
    | (have j0 := eq385 X0 X1
       grind)
    | exact resolve eq385 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq397 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq380 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq380
    | (have j0 := eq380 (τ X0)
       grind)
    | exact resolve eq380 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq407 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq397 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq397
    | (have j0 := eq397 X0
       grind)
    | exact resolve eq397 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq414 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq407 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq407
    | (have j0 := eq407 X0
       grind)
    | exact resolve eq407 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq579 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X3)) X0) X2) X4) X0) ≠ X4 ∨ (k X4 (M.op (M.op (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X3)) X0) X2) X4) X0)) = (M.op X4 (M.op (M.op (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X3)) X0) X2) X4) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq63 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq63
    | exact resolve eq63 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq63
  have eq597 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq73 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq679 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2) (M.op (M.op X0 X0) X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq224 X0 (M.op (M.op X0 X0) X1) X2
       have i₂ := eq90 (M.op X0 X0) X1
       grind)
    | exact superpose eq90 eq224
    | exact resolve eq224 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq1008 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq75 X0
       have i₂ := eq90 X0 X0
       grind)
    | exact superpose eq90 eq75
    | (have j0 := eq75 X0
       grind)
    | exact resolve eq75 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq1558 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq200 X0 (k X0 X0)
       have i₂ := eq381 X0
       grind)
    | exact superpose eq381 eq200
    | (have j0 := eq200 X0 X0
       have j1 := eq381 X0
       grind)
    | exact resolve eq200 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq381
  have eq1589 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq1558 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1558
  have eq1593 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1589 X0
       have j1 := eq380 X0
       grind)
    | (have r₁ := eq1589 X0
       have r₂ := eq380 X0
       grind)
    | exact resolve eq1589 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380 eq1589
  have eq1872 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq26 (τ X0) X0 (τ X0)
       have i₂ := eq1593 (τ X0)
       grind)
    | exact superpose eq1593 eq26
    | (have j1 := eq1593 (τ X0)
       grind)
    | exact resolve eq26 eq1593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1875 : ∀ X0 : G, (τ (σ X0)) = (k X0 (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 (k X0 X0))
       have i₂ := eq1593 X0
       grind)
    | exact superpose eq1593 eq10
    | (have j1 := eq1593 X0
       grind)
    | exact resolve eq10 eq1593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1593
  have eq1898 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1875 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1875
    | (have j0 := eq1875 X0
       grind)
    | exact resolve eq1875 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1875
  have eq1901 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1872 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1872
    | (have j0 := eq1872 X0
       grind)
    | exact resolve eq1872 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1872
  have eq1913 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1901 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1901
    | (have j0 := eq1901 X0
       grind)
    | exact resolve eq1901 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1901
  have eq1932 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1913 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq1913
    | (have j0 := eq1913 X0
       have j1 := eq14 X0 X0
       grind)
    | exact resolve eq1913 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1913
  have eq1951 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1932 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1932
  have eq2040 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq107 (σ X0) (σ X0)
       have i₂ := eq1898 X0
       grind)
    | exact superpose eq1898 eq107
    | (have j1 := eq1898 X0
       grind)
    | (have r₁ := eq107 (σ X0) (σ X0)
       have r₂ := eq1898 X0
       grind)
    | exact resolve eq107 eq1898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq2059 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) (σ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1008 (σ X0)
       have i₂ := eq1898 X0
       grind)
    | exact superpose eq1898 eq1008
    | (have j1 := eq1898 X0
       grind)
    | (have r₁ := eq1008 (σ X0)
       have r₂ := eq1898 X0
       grind)
    | exact resolve eq1008 eq1898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1898
  have eq2060 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq2059 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059
  have eq2062 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq2040 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040
  have eq2066 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2060 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq2060
    | (have j0 := eq2060 X0
       grind)
    | exact resolve eq2060 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2060
  have eq2073 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2062 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq2062
    | (have j0 := eq2062 X0
       grind)
    | exact resolve eq2062 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2062
  have eq4437 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (k (σ X0) (σ (k X0 X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1008 (σ X0)
       have i₂ := eq2073 X0
       grind)
    | exact superpose eq2073 eq1008
    | (have j1 := eq2073 X0
       grind)
    | exact resolve eq1008 eq2073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2073
  have eq4446 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ X0) (σ (k X0 X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq4437 X0
       have j1 := eq2066 X0
       grind)
    | (have r₁ := eq4437 X0
       have r₂ := eq2066 X0
       grind)
    | exact resolve eq4437 eq2066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2066 eq4437
  have eq4455 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k X0 (k X0 X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq4446 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq4446
    | (have j0 := eq4446 X0
       grind)
    | exact resolve eq4446 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4446
  have eq5859 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq361
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq361
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq361 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq5860 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq5859
  have eq6195 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ (τ X1)) X2) (σ (τ (k X0 X1)))) X2) = X2 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq363 (τ X0) (τ X1) X2
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq363
    | (have j0 := eq363 (τ X0) (τ X0) X2
       grind)
    | exact resolve eq363 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq363
  have eq6289 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ (τ X1)) X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6195 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq6195
    | (have j0 := eq6195 X0 X0 X2
       grind)
    | exact resolve eq6195 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6195
  have eq6300 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6289 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6289
    | (have j0 := eq6289 X0 X0 X2
       grind)
    | exact resolve eq6289 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6289
  have eq6302 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op X1 X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6300 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6300
    | (have j0 := eq6300 X0 X1 X2
       grind)
    | exact resolve eq6300 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6300
  have eq6303 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op X1 X2) (k X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6302 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6302
    | (have j0 := eq6302 X0 X1 X2
       grind)
    | exact resolve eq6302 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6302
  have eq6304 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (k X0 X1)) X2) = X2 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6303 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6303
    | (have j0 := eq6303 X0 X1 X2
       grind)
    | exact resolve eq6303 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6303
  have eq13913 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k X0 (k X0 X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 (k X0 X0))
       have i₂ := eq4455 X0
       grind)
    | exact superpose eq4455 eq10
    | (have j1 := eq4455 X0
       grind)
    | exact resolve eq10 eq4455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4455
  have eq13957 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13913 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq13913
    | (have j0 := eq13913 X0
       grind)
    | exact resolve eq13913 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13913
  have eq14026 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13957 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq13957
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq13957 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13957
  have eq14146 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq14026 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14026
  have eq14172 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq14146 X0
       have j1 := eq1008 X0
       grind)
    | (have r₁ := eq14146 X0
       have r₂ := eq1008 X0
       grind)
    | exact resolve eq14146 eq1008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008 eq14146
  have eq14411 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq14172 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14172
  have eq14424 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq14411 X0
       have j1 := eq1951 X0
       grind)
    | (have r₁ := eq14411 X0
       have r₂ := eq1951 X0
       grind)
    | exact resolve eq14411 eq1951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1951 eq14411
  have eq14605 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq14424 (σ X0)
       grind)
    | exact superpose eq14424 eq28
    | exact resolve eq28 eq14424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq14635 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14605 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14605
    | exact resolve eq14605 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14605
  have eq19944 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) ≠ X0 ∨ (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X0) = (k (M.op (M.op X0 X0) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq579 x x x x (M.op (M.op x x) (M.op x x))
       have i₂ := eq679 x (M.op x x) x
       grind)
    | exact superpose eq679 eq579
    | exact resolve eq579 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579 eq679
  have eq20020 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) ≠ X0 ∨ (k (M.op (M.op X0 X0) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19944 X0 X1
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq19944
    | (have j0 := eq19944 X0 X1
       grind)
    | exact resolve eq19944 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19944
  have eq35861 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 (k X1 X0)) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (k X1 X0)
       have i₂ := eq6304 X1 X0 X0
       grind)
    | exact superpose eq6304 eq76
    | (have j1 := eq6304 X1 X1 x
       grind)
    | exact resolve eq76 eq6304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6304
  have eq39070 : y = (k y (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14635 y
       have i₂ := eq5860
       grind)
    | exact superpose eq5860 eq14635
    | exact resolve eq14635 eq5860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5860 eq14635
  have eq39279 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39070
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq39070
    | exact resolve eq39070 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39070
  have eq39294 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq414 y
       grind)
    | (have r₁ := eq39279
       have r₂ := eq414 y
       grind)
    | exact resolve eq39279 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414 eq39279
  have eq39397 : (σ x) ≠ (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (σ x) = (k (M.op (M.op (σ x) (σ x)) (σ x)) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20020 (σ x) (σ y)
       have i₂ := eq39294
       grind)
    | exact superpose eq39294 eq20020
    | exact resolve eq20020 eq39294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20020 eq39294
  have eq39403 : (σ x) = (k (M.op (M.op (σ x) (σ x)) (σ x)) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq39397
       have r₂ := eq68 (σ x)
       grind)
    | exact resolve eq39397 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39397
  have eq39442 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39403
       have i₂ := eq68 (σ x)
       grind)
    | exact superpose eq68 eq39403
    | exact resolve eq39403 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq39403
  have eq39450 : (σ x) = (σ (k x x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39442
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq39442
    | exact resolve eq39442 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39442
  have eq39469 : (τ (σ x)) = (k x x) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq39450
       grind)
    | exact superpose eq39450 eq10
    | exact resolve eq10 eq39450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39450
  have eq39586 : y = (M.op y y) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39469
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq39469
    | exact resolve eq39469 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39469
  have eq39597 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (k x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq76 y X0
       have i₂ := eq39586
       grind)
    | exact superpose eq39586 eq76
    | exact resolve eq76 eq39586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39695 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (k x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq597 y y x
       have i₂ := eq39586
       grind)
    | exact superpose eq39586 eq597
    | exact resolve eq597 eq39586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39586
  have eq39741 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (k x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq39695 X0
       have i₂ := eq90 y X0
       grind)
    | exact superpose eq90 eq39695
    | exact resolve eq39695 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39695
  have eq41852 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (k x x) ∨ x = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq39597 X0
       have i₂ := eq39741 X0
       grind)
    | exact superpose eq39741 eq39597
    | exact resolve eq39597 eq39741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39597 eq39741
  have eq42017 : ∀ X0 : G, x = (k x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq41852 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41852
  have eq42537 : ∀ X0 : G, x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq35861 x x
       have i₂ := eq42017 X0
       grind)
    | exact superpose eq42017 eq35861
    | (have j0 := eq35861 x x
       have j1 := eq42017 X0
       grind)
    | exact resolve eq35861 eq42017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35861 eq42017
  have eq42540 : ∀ X0 : G, x = (M.op x y) ∨ (M.op y X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq42537 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42537
  have eq42612 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq90 x y
       have i₂ := eq42540 X0
       grind)
    | exact superpose eq42540 eq90
    | (have j1 := eq42540 X0
       grind)
    | exact resolve eq90 eq42540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42540
  have eq42684 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq42612 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42612
  have eq42738 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq76 x X0
       have i₂ := eq42684 X1
       grind)
    | exact superpose eq42684 eq76
    | (have j1 := eq42684 X1
       grind)
    | exact resolve eq76 eq42684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42771 : ∀ X0 : G, x = (k x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14424 x
       have i₂ := eq42684 X0
       grind)
    | exact superpose eq42684 eq14424
    | (have j1 := eq42684 X0
       grind)
    | exact resolve eq14424 eq42684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42836 : ∀ X0 X1 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq597 x x x
       have i₂ := eq42684 X0
       grind)
    | exact superpose eq42684 eq597
    | (have j1 := eq42684 X1
       grind)
    | exact resolve eq597 eq42684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42684
  have eq42885 : ∀ X0 X1 : G, x = (M.op (M.op x X0) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42836 X0 X1
       have i₂ := eq90 x X0
       grind)
    | exact superpose eq90 eq42836
    | (have j0 := eq42836 X0 X1
       grind)
    | exact resolve eq42836 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42836
  have eq43013 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq392 x x
       have i₂ := eq42771 X0
       grind)
    | exact superpose eq42771 eq392
    | (have j0 := eq392 x x
       have j1 := eq42771 X0
       grind)
    | exact resolve eq392 eq42771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42771
  have eq43036 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq43013 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43013
  have eq43037 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq43036 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43036
  have eq44282 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq76 (σ x) X0
       have i₂ := eq43037 X1
       grind)
    | exact superpose eq43037 eq76
    | (have j1 := eq43037 X1
       grind)
    | exact resolve eq76 eq43037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq44380 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ x)) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq597 (σ x) (σ x) x
       have i₂ := eq43037 X0
       grind)
    | exact superpose eq43037 eq597
    | (have j1 := eq43037 X1
       grind)
    | exact resolve eq597 eq43037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43037
  have eq44436 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) (σ x)) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq44380 X0 X1
       have i₂ := eq90 (σ x) X0
       grind)
    | exact superpose eq90 eq44380
    | (have j0 := eq44380 X0 X1
       grind)
    | exact resolve eq44380 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44380
  have eq45874 : ∀ X0 X1 X2 : G, (M.op y X2) = X2 ∨ (M.op y X1) = X1 ∨ (M.op x X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42738 X0 X2
       have i₂ := eq42885 X0 X1
       grind)
    | exact superpose eq42885 eq42738
    | (have j0 := eq42738 X0 X2
       have j1 := eq42885 X0 X2
       grind)
    | exact resolve eq42738 eq42885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42738 eq42885
  have eq49711 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op y X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq45874 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45874
  have eq49712 : ∀ X0 X1 : G, (M.op y X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq49711 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49711
  have eq49746 : ∀ X0 X1 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq77 y X0
       have i₂ := eq49712 y X1
       grind)
    | exact superpose eq49712 eq77
    | (have j1 := eq49712 X0 X1
       grind)
    | exact resolve eq77 eq49712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50062 : ∀ X0 X1 : G, y = (M.op (M.op y X0) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49746 X0 X1
       have i₂ := eq90 y X0
       grind)
    | exact superpose eq90 eq49746
    | (have j0 := eq49746 X0 X1
       grind)
    | exact resolve eq49746 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq49746
  have eq51229 : ∀ X0 X1 X2 : G, y = (M.op X0 y) ∨ (M.op x X1) = X1 ∨ (M.op x X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50062 X0 X1
       have i₂ := eq49712 X0 X2
       grind)
    | exact superpose eq49712 eq50062
    | (have j0 := eq50062 X0 X1
       have j1 := eq49712 X0 X1
       grind)
    | exact resolve eq50062 eq49712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49712 eq50062
  have eq59636 : ∀ X0 : G, y ≠ y ∨ (M.op x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq51229 x X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51229
  have eq59637 : ∀ X0 : G, y = (M.op x y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq59636 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59636
  have eq59795 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq59637 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59637
  have eq59796 : y = (M.op x y) := by grind
  clear eq59795
  have eq69937 : ∀ X0 X1 X2 : G, (M.op (σ x) X0) = X0 ∨ (M.op y X1) = X1 ∨ (M.op y X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44282 X0 X1
       have i₂ := eq44436 X0 X2
       grind)
    | exact superpose eq44436 eq44282
    | (have j0 := eq44282 X0 X1
       have j1 := eq44436 X0 X1
       grind)
    | exact resolve eq44282 eq44436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44282 eq44436
  have eq75688 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op y X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq69937 (σ y) X0 X1
       grind)
    | exact superpose eq69937 eq16
    | (have j1 := eq69937 X0 X0 X0
       grind)
    | exact resolve eq16 eq69937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69937
  have eq76054 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ (M.op y X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq75688 X0 X1
       have i₂ := eq59796
       grind)
    | exact superpose eq59796 eq75688
    | (have j0 := eq75688 X0 X0
       grind)
    | exact resolve eq75688 eq59796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59796 eq75688
  have eq76055 : ∀ X0 X1 : G, (M.op y X1) = X1 ∨ (M.op y X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq76054 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76054
  have eq76427 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq76055 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76055
  have eq76428 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq76427 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76427
  have eq76521 : y = (k y y) := by
    first
    | (have i₁ := eq14424 y
       have i₂ := eq76428 y
       grind)
    | exact superpose eq76428 eq14424
    | exact resolve eq14424 eq76428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14424
  have eq76587 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op y X1) X0) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq597 y X1 X0
       have i₂ := eq76428 X0
       grind)
    | exact superpose eq76428 eq597
    | exact resolve eq597 eq76428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq76670 : ∀ X0 : G, y = (M.op (M.op (M.op y y) X0) y) := by
    intro X0
    first
    | (have i₁ := eq77 y X0
       have i₂ := eq76428 (M.op (M.op y y) X0)
       grind)
    | exact superpose eq76428 eq77
    | exact resolve eq77 eq76428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq76907 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq76670 X0
       have i₂ := eq76428 y
       grind)
    | exact superpose eq76428 eq76670
    | exact resolve eq76670 eq76428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76670
  have eq76963 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq76587 X0 X0
       have i₂ := eq76428 X0
       grind)
    | exact superpose eq76428 eq76587
    | exact resolve eq76587 eq76428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76587
  have eq77103 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq76907 X0
       have i₂ := eq76428 X0
       grind)
    | exact superpose eq76428 eq76907
    | exact resolve eq76907 eq76428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76428 eq76907
  have eq77297 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq392 y y
       have i₂ := eq76521
       grind)
    | exact superpose eq76521 eq392
    | (have j0 := eq392 y x
       grind)
    | exact resolve eq392 eq76521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392 eq76521
  have eq77320 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq77297
  have eq77321 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq77320
  have eq82608 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (σ y)
       have i₂ := eq77321
       grind)
    | exact superpose eq77321 eq9
    | exact resolve eq9 eq77321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77321
  have eq82787 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq82608 X0
       have i₂ := eq76963 X0 (σ y)
       grind)
    | exact superpose eq76963 eq82608
    | exact resolve eq82608 eq76963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82608
  have eq83028 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq76963 X0 (σ y)
       have i₂ := eq82787 X0
       grind)
    | exact superpose eq82787 eq76963
    | exact resolve eq76963 eq82787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76963 eq82787
  have eq84059 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq83028 (σ x)
       grind)
    | exact superpose eq83028 eq16
    | exact resolve eq16 eq83028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83028
  have eq84147 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq84059
       have i₂ := eq77103 x
       grind)
    | exact superpose eq77103 eq84059
    | exact resolve eq84059 eq77103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77103 eq84059
  have eq84148 : False := by grind
  exact eq84148

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(X,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_x_pyy_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X0 X0) X0 X2
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq61
    | exact resolve eq61 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq90 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq76
    | exact resolve eq76 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq391 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq413 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) ∨ (σ (σ X1)) = (M.op (σ (σ X1)) (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq391 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq391
    | (have j0 := eq391 (σ X0) (σ X0)
       grind)
    | exact resolve eq391 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq417 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq391 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq391
    | (have j0 := eq391 X1 X1
       have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq391 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq566 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq73 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq15648 : ∀ X0 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq413 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq15650 : ∀ X0 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq15648 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15648
  have eq15734 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq417 x y
       grind)
    | exact superpose eq417 eq16
    | (have j1 := eq417 y y
       grind)
    | (have r₁ := eq16
       have r₂ := eq417 x y
       grind)
    | exact resolve eq16 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq15881 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq15734
  have eq17793 : ∀ X0 : G, (σ (σ (τ X0))) ≠ (σ (k (σ (τ X0)) X0)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq15650 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq15650
    | (have j0 := eq15650 (τ X0)
       grind)
    | exact resolve eq15650 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15650
  have eq17805 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq17793 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17793
    | (have j0 := eq17793 X0
       grind)
    | exact resolve eq17793 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17793
  have eq17812 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq17805 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17805
    | (have j0 := eq17805 X0
       grind)
    | exact resolve eq17805 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17805
  have eq17820 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17812 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq17812
    | (have j0 := eq17812 (τ X0)
       grind)
    | exact resolve eq17812 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq17812
  have eq17832 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17820 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17820
    | (have j0 := eq17820 X0
       grind)
    | exact resolve eq17820 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17820
  have eq17839 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17832 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17832
    | (have j0 := eq17832 X0
       grind)
    | exact resolve eq17832 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17832
  have eq25738 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ y)
       have i₂ := eq15881
       grind)
    | exact superpose eq15881 eq12
    | (have r₁ := eq12 (σ y) (σ y)
       have r₂ := eq15881
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq15881
       grind)
    | (have r₁ := eq12 y y
       have r₂ := eq15881
       grind)
    | exact resolve eq12 eq15881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15881
  have eq25831 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq25738
  have eq25869 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25831
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq25831
    | exact resolve eq25831 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25831
  have eq48399 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90 (σ x) (σ y)
       have i₂ := eq25869
       grind)
    | exact superpose eq25869 eq90
    | exact resolve eq90 eq25869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25869
  have eq53257 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq107 (σ x) (σ x)
       have i₂ := eq48399
       grind)
    | exact superpose eq48399 eq107
    | (have r₁ := eq107 (σ x) (σ x)
       have r₂ := eq48399
       grind)
    | (have r₁ := eq107 y y
       have r₂ := eq48399
       grind)
    | (have r₁ := eq107 x y
       have r₂ := eq48399
       grind)
    | exact resolve eq107 eq48399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq48399
  have eq53381 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq53257
  have eq53426 : (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq53381
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq53381
    | exact resolve eq53381 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53381
  have eq53485 : (τ (σ y)) = (k y y) ∨ (σ x) = (σ (k x x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq53426
       grind)
    | exact superpose eq53426 eq10
    | exact resolve eq10 eq53426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53426
  have eq53638 : y = (k y y) ∨ (σ x) = (σ (k x x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq53485
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq53485
    | exact resolve eq53485 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53485
  have eq53647 : (σ x) = (σ (k x x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq17839 y
       grind)
    | (have r₁ := eq53638
       have r₂ := eq17839 y
       grind)
    | exact resolve eq53638 eq17839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17839 eq53638
  have eq53662 : (τ (σ x)) = (k x x) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq53647
       grind)
    | exact superpose eq53647 eq10
    | exact resolve eq10 eq53647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53647
  have eq53815 : y = (M.op y y) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq53662
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq53662
    | exact resolve eq53662 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53662
  have eq53831 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (k x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq76 y X0
       have i₂ := eq53815
       grind)
    | exact superpose eq53815 eq76
    | exact resolve eq76 eq53815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53924 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (k x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq566 y y x
       have i₂ := eq53815
       grind)
    | exact superpose eq53815 eq566
    | exact resolve eq566 eq53815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53815
  have eq54059 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (k x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq53924 X0
       have i₂ := eq90 y X0
       grind)
    | exact superpose eq90 eq53924
    | exact resolve eq53924 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53924
  have eq55997 : ∀ X0 : G, x = (k x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq54059 eq53831
    | exact resolve eq53831 eq54059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53831 eq54059
  have eq56035 : ∀ X0 : G, x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 x x
       have i₂ := eq55997 X0
       grind)
    | exact superpose eq55997 eq14
    | (have j0 := eq14 x x
       have j1 := eq55997 X0
       grind)
    | exact resolve eq14 eq55997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55997
  have eq56036 : ∀ X0 : G, x = (M.op x y) ∨ (M.op y X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq56035 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56035
  have eq57761 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq90 x y
       have i₂ := eq56036 X0
       grind)
    | exact superpose eq56036 eq90
    | (have j1 := eq56036 X0
       grind)
    | exact resolve eq90 eq56036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56036
  have eq57889 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq57761 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57761
  have eq58067 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq76 x X0
       have i₂ := eq57889 X1
       grind)
    | exact superpose eq57889 eq76
    | (have j1 := eq57889 X1
       grind)
    | exact resolve eq76 eq57889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq58160 : ∀ X0 X1 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq566 x x x
       have i₂ := eq57889 X0
       grind)
    | exact superpose eq57889 eq566
    | (have j1 := eq57889 X1
       grind)
    | exact resolve eq566 eq57889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57889
  have eq58298 : ∀ X0 X1 : G, x = (M.op (M.op x X0) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq58160 X0 X1
       have i₂ := eq90 x X0
       grind)
    | exact superpose eq90 eq58160
    | (have j0 := eq58160 X0 X1
       grind)
    | exact resolve eq58160 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq58160
  have eq59937 : ∀ X0 X1 : G, (M.op y X1) = X1 ∨ (M.op x X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq58298 eq58067
    | (have j0 := eq58067 X0 X1
       have j1 := eq58298 X0 X1
       grind)
    | exact resolve eq58067 eq58298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58067
  have eq59938 : ∀ X0 X1 : G, x = (M.op X0 x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq59937 eq58298
    | (have j0 := eq58298 X0 X1
       have j1 := eq59937 X0 X1
       grind)
    | exact resolve eq58298 eq59937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58298
  have eq59946 : ∀ X0 : G, y ≠ y ∨ (M.op y y) = (k y y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq75 y
       have i₂ := eq59937 X0 y
       grind)
    | exact superpose eq59937 eq75
    | (have j1 := eq59937 X0 x
       grind)
    | (have r₁ := eq75 y
       have r₂ := eq59937 X0 y
       grind)
    | (have r₁ := eq75 x
       have r₂ := eq59937 x x
       grind)
    | exact resolve eq75 eq59937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60041 : ∀ X0 X1 X2 : G, (M.op y X1) = (M.op (M.op (M.op y X1) X0) (M.op y X1)) ∨ (M.op x X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq566 y X1 X0
       have i₂ := eq59937 X2 X0
       grind)
    | exact superpose eq59937 eq566
    | (have j1 := eq59937 X2 X1
       grind)
    | exact resolve eq566 eq59937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq60180 : ∀ X0 X1 : G, y = (M.op (M.op (M.op y y) X0) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq77 y X0
       have i₂ := eq59937 X1 (M.op (M.op y y) X0)
       grind)
    | exact superpose eq59937 eq77
    | (have j1 := eq59937 X1 X1
       grind)
    | exact resolve eq77 eq59937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60361 : ∀ X0 : G, (M.op y y) = (k y y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq59946 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59946
  have eq60474 : ∀ X0 X1 : G, y = (M.op (M.op y X0) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq59937 eq60180
    | (have j0 := eq60180 X0 X1
       have j1 := eq59937 X1 X1
       grind)
    | exact resolve eq60180 eq59937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60180
  have eq60554 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X1) = X1 ∨ (M.op x X2) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq59937 eq60041
    | (have j0 := eq60041 X0 X1 X2
       have j1 := eq59937 X2 X1
       grind)
    | exact resolve eq60041 eq59937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60041
  have eq60629 : ∀ X0 : G, y = (k y y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | exact superpose eq59937 eq60361
    | (have j0 := eq60361 X0
       have j1 := eq59937 X0 x
       grind)
    | exact resolve eq60361 eq59937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60361
  have eq60696 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq59937 eq60474
    | (have j0 := eq60474 X0 X1
       have j1 := eq59937 X1 X1
       grind)
    | exact resolve eq60474 eq59937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60474
  have eq61921 : x ≠ x ∨ x = (M.op y x) := by
    first
    | (have j0 := eq59938 y x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59938
  have eq61922 : x = (M.op y x) := by grind
  clear eq61921
  have eq62808 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (M.op y X0) x) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 y x X1
       have i₂ := eq61922
       grind)
    | exact superpose eq61922 eq61
    | exact resolve eq61 eq61922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61922
  have eq63415 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq391 y y
       have i₂ := eq60629 X0
       grind)
    | exact superpose eq60629 eq391
    | (have j0 := eq391 y y
       have j1 := eq60629 X0
       grind)
    | exact resolve eq391 eq60629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60629
  have eq63418 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq63415 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63415
  have eq64230 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq60696 x y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64231 : y = (M.op x y) := by grind
  clear eq64230
  have eq65114 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq64231
       grind)
    | exact superpose eq64231 eq16
    | exact resolve eq16 eq64231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65122 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (M.op x X0) y) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 x y X1
       have i₂ := eq64231
       grind)
    | exact superpose eq64231 eq61
    | exact resolve eq61 eq64231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq64231
  have eq75163 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (σ y) (σ y)
       have i₂ := eq63418 X1
       grind)
    | exact superpose eq63418 eq9
    | (have j1 := eq63418 X1
       grind)
    | exact resolve eq9 eq63418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63418
  have eq75397 : ∀ X0 X1 : G, (M.op (σ y) X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq60554 eq75163
    | (have j0 := eq75163 X0 X1
       have j1 := eq60554 X0 X1 X1
       grind)
    | exact resolve eq75163 eq60554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60554 eq75163
  have eq77497 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (M.op x (σ y)) y) X0) (σ y)) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65122 (σ y) X0
       have i₂ := eq75397 (M.op (M.op (M.op x (σ y)) y) X0) X1
       grind)
    | exact superpose eq75397 eq65122
    | (have j1 := eq75397 X0 X1
       grind)
    | exact resolve eq65122 eq75397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65122 eq75397
  have eq77706 : ∀ X0 X1 : G, (σ y) = (M.op (M.op y X0) (σ y)) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq60696 eq77497
    | (have j0 := eq77497 X0 X1
       have j1 := eq60696 X0 X1
       grind)
    | exact resolve eq77497 eq60696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60696 eq77497
  have eq77710 : ∀ X0 X1 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq59937 eq77706
    | (have j0 := eq77706 X0 X1
       have j1 := eq59937 X1 X1
       grind)
    | exact resolve eq77706 eq59937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59937 eq77706
  have eq80877 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq65114
       have i₂ := eq77710 (σ x) X0
       grind)
    | exact superpose eq77710 eq65114
    | (have j1 := eq77710 X0 X0
       grind)
    | (have r₁ := eq65114
       have r₂ := eq77710 (σ x) x
       grind)
    | exact resolve eq65114 eq77710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77710
  have eq80918 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq80877 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80877
  have eq81749 : x ≠ x ∨ (k x x) = (M.op x x) := by
    first
    | (have i₁ := eq75 x
       have i₂ := eq80918 x
       grind)
    | exact superpose eq80918 eq75
    | (have r₁ := eq75 x
       have r₂ := eq80918 x
       grind)
    | exact resolve eq75 eq80918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq81996 : ∀ X0 : G, x = (M.op (M.op (M.op x x) X0) x) := by
    intro X0
    first
    | (have i₁ := eq77 x X0
       have i₂ := eq80918 (M.op (M.op x x) X0)
       grind)
    | exact superpose eq80918 eq77
    | exact resolve eq77 eq80918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq82185 : (k x x) = (M.op x x) := by grind
  clear eq81749
  have eq82301 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq81996 X0
       have i₂ := eq80918 x
       grind)
    | exact superpose eq80918 eq81996
    | exact resolve eq81996 eq80918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81996
  have eq82468 : x = (k x x) := by
    first
    | (have i₁ := eq82185
       have i₂ := eq80918 x
       grind)
    | exact superpose eq80918 eq82185
    | exact resolve eq82185 eq80918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82185
  have eq82536 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq82301 X0
       have i₂ := eq80918 X0
       grind)
    | exact superpose eq80918 eq82301
    | exact resolve eq82301 eq80918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82301
  have eq83299 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq391 x x
       have i₂ := eq82468
       grind)
    | exact superpose eq82468 eq391
    | (have j0 := eq391 x x
       grind)
    | exact resolve eq391 eq82468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391 eq82468
  have eq83302 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq83299
  have eq83322 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq62808 X0 X1
       have i₂ := eq82536 (M.op y X0)
       grind)
    | exact superpose eq82536 eq62808
    | exact resolve eq62808 eq82536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62808 eq82536
  have eq84742 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq83322 X0 X1
       have i₂ := eq80918 X1
       grind)
    | exact superpose eq80918 eq83322
    | exact resolve eq83322 eq80918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80918 eq83322
  have eq85556 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ x)
       have i₂ := eq83302
       grind)
    | exact superpose eq83302 eq9
    | exact resolve eq9 eq83302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83302
  have eq85717 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq85556 X0
       have i₂ := eq84742 (σ x) X0
       grind)
    | exact superpose eq84742 eq85556
    | exact resolve eq85556 eq84742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84742 eq85556
  have eq85761 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq65114
       have i₂ := eq85717 (σ y)
       grind)
    | exact superpose eq85717 eq65114
    | (have r₁ := eq65114
       have r₂ := eq85717 (σ y)
       grind)
    | exact resolve eq65114 eq85717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65114 eq85717
  have eq85976 : False := by grind
  exact eq85976

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pyy_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq174 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq178 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : x ≠ (M.op x y) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq174 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq174
    | (have j0 := eq174 y
       grind)
    | exact resolve eq174 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq190 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq175
    | (have j0 := eq175 (σ y)
       grind)
    | exact resolve eq175 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq199 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op x X0) (M.op x y)) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq607 : (M.op x y) = (k y x) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
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
  have eq609 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq628 : y = (k y (M.op (M.op x y) (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op y y) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq183
       have i₂ := eq11 y (M.op sF0 sF0)
       grind)
    | exact superpose eq11 eq183
    | (have j1 := eq11 (M.op x y) (M.op y y)
       grind)
    | exact resolve eq183 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq635 : (σ y) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq190
       have i₂ := eq11 sF3 (M.op sF4 sF4)
       grind)
    | exact superpose eq11 eq190
    | (have j1 := eq11 (M.op (σ x) (σ y)) (M.op (σ y) (σ y))
       grind)
    | exact resolve eq190 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq680 : (σ y) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have j1 := eq12 (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq635
       have r₂ := eq12 (M.op (σ x) (σ y)) (M.op (σ y) (σ y))
       grind)
    | (have r₁ := eq635
       have r₂ := eq12 (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq635
       have r₂ := eq12 (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y))
       grind)
    | exact resolve eq635 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq684 : y = (k y (M.op (M.op x y) (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have j1 := eq12 y (M.op (M.op x y) (M.op x y))
       grind)
    | (have r₁ := eq628
       have r₂ := eq12 (M.op x y) (M.op y y)
       grind)
    | (have r₁ := eq628
       have r₂ := eq12 y (M.op (M.op x y) (M.op x y))
       grind)
    | (have r₁ := eq628
       have r₂ := eq12 (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) y)
       grind)
    | exact resolve eq628 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq695 : (σ y) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq190 eq680
    | exact resolve eq680 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq680
  have eq699 : y = (k y (M.op (M.op x y) (M.op x y))) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq183 eq684
    | exact resolve eq684 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq684
  have eq800 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq607
       grind)
    | exact superpose eq607 eq39
    | exact resolve eq39 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq801 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq800
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq800
    | exact resolve eq800 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq803 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq801
    | exact resolve eq801 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq865 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | exact superpose eq177 eq199
    | exact resolve eq199 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq876 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq865 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq865
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq865 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq886 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) X0
       have i₂ := eq865 X0
       grind)
    | exact superpose eq865 eq16
    | exact resolve eq16 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq888 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq876 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876
  have eq932 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq886 X0 (M.op X0 X1)
       have i₂ := eq16 X0 X0 X1
       grind)
    | exact superpose eq16 eq886
    | exact resolve eq886 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq936 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq177 eq886
    | exact resolve eq886 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq940 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq178 eq886
    | exact resolve eq886 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq886
  have eq950 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq936
       have i₂ := eq11 sF0 x
       grind)
    | exact superpose eq11 eq936
    | (have j1 := eq11 (M.op x y) x
       grind)
    | exact resolve eq936 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq960 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have j1 := eq12 (M.op x y) x
       grind)
    | (have r₁ := eq950
       have r₂ := eq12 (M.op x y) x
       grind)
    | exact resolve eq950 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq961 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq936 eq960
    | exact resolve eq960 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq962 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq940
       have i₂ := eq11 sF4 sF2
       grind)
    | exact superpose eq11 eq940
    | (have j1 := eq11 (M.op (σ x) (σ y)) (σ x)
       grind)
    | exact resolve eq940 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq972 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have j1 := eq12 (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq962
       have r₂ := eq12 (M.op (σ x) (σ y)) (σ x)
       grind)
    | exact resolve eq962 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq973 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq940 eq972
    | exact resolve eq972 eq940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972
  have eq1166 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq961 eq39
    | exact resolve eq39 eq961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq961
  have eq1167 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1166
    | exact resolve eq1166 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166
  have eq1643 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq865 X0
       have i₂ := eq593 X0
       grind)
    | exact superpose eq593 eq865
    | (have j1 := eq593 X0
       grind)
    | exact resolve eq865 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1658 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq593 X0
       grind)
    | exact superpose eq593 eq13
    | (have j0 := eq13 X0 (M.op X0 X0)
       have j1 := eq593 X0
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq593 X0
       grind)
    | exact resolve eq13 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1666 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq932 (M.op X0 X0) X0
       have i₂ := eq593 X0
       grind)
    | exact superpose eq593 eq932
    | (have j1 := eq593 X0
       grind)
    | exact resolve eq932 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593 eq932
  have eq1667 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq1658 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1658
  have eq1672 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | exact superpose eq1666 eq1667
    | (have j0 := eq1667 X0
       have j1 := eq1666 X0
       grind)
    | exact resolve eq1667 eq1666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1666 eq1667
  have eq1682 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq1643 eq1672
    | (have j0 := eq1672 X0
       have j1 := eq1643 X0
       grind)
    | exact resolve eq1672 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1643 eq1672
  have eq1841 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq803 eq609
    | exact resolve eq609 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1851 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1841
       have r₂ := eq27
       grind)
    | exact resolve eq1841 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1841
  have eq1873 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1851 eq865
    | exact resolve eq865 eq1851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1851
  have eq1881 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1873
    | exact resolve eq1873 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1873
  have eq1895 : x = (k y y) ∨ x = y ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq1881
       grind)
    | exact superpose eq1881 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1896 : x ≠ y ∨ x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq1881
       grind)
    | exact superpose eq1881 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1881
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1881
       grind)
    | exact resolve eq13 eq1881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1907 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq865 y
       have i₂ := eq1881
       grind)
    | exact superpose eq1881 eq865
    | exact resolve eq865 eq1881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1881
  have eq1912 : x = (k y y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1895
  have eq1914 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1907
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1907
    | exact resolve eq1907 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1907
  have eq1918 : x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1912
       have r₂ := eq1896
       grind)
    | exact resolve eq1912 eq1896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1896 eq1912
  have eq1923 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1914 eq1918
    | exact resolve eq1918 eq1914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1918
  have eq1926 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1914 eq27
    | exact resolve eq27 eq1914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1949 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1914 eq973
    | exact resolve eq973 eq1914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973
  have eq1952 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  have eq1954 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1949
       have r₂ := eq1952
       grind)
    | exact resolve eq1949 eq1952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1949 eq1952
  have eq1961 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1923 eq41
    | exact resolve eq41 eq1923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1923
  have eq1968 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1961
    | exact resolve eq1961 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1961
  have eq1971 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1968
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1968
    | exact resolve eq1968 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1968
  have eq2016 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1954 eq803
    | exact resolve eq803 eq1954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803 eq1954
  have eq2024 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2016
  have eq2030 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2024
       have r₂ := eq1926
       grind)
    | exact resolve eq2024 eq1926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1926 eq2024
  have eq2069 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq865 y
       have i₂ := eq2030
       grind)
    | exact superpose eq2030 eq865
    | exact resolve eq865 eq2030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865 eq2030
  have eq2076 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2069
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2069
    | exact resolve eq2069 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2069
  have eq2077 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2076
  have eq2088 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2077 eq181
    | (have r₁ := eq181
       have r₂ := eq2077
       grind)
    | exact resolve eq181 eq2077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2097 : (σ y) = (k (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2077 eq695
    | exact resolve eq695 eq2077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2106 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2077 eq940
    | exact resolve eq940 eq2077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2077
  have eq2111 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2088
  have eq2118 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2106 eq2097
    | exact resolve eq2097 eq2106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2097
  have eq2124 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2106 eq2111
    | exact resolve eq2111 eq2106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2111
  have eq2129 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2106 eq2118
    | exact resolve eq2118 eq2106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2118
  have eq2131 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2124 eq2129
    | exact resolve eq2129 eq2124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2124 eq2129
  have eq2132 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2131
  have eq2135 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2132 eq31
    | exact resolve eq31 eq2132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2200 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq2135
    | exact resolve eq2135 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2135
  have eq2211 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq2200
       grind)
    | exact superpose eq2200 eq24
    | exact resolve eq24 eq2200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2200
  have eq2251 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq2211
    | exact resolve eq2211 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2211
  have eq2262 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2251 eq1167
    | exact resolve eq1167 eq2251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167
  have eq2265 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2251 eq1971
    | exact resolve eq1971 eq2251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1971
  have eq2268 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2265
  have eq2271 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2262
  have eq2272 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1914 eq2268
    | exact resolve eq2268 eq1914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2268
  have eq2273 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2272
  have eq2477 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2106 eq1682
    | (have j0 := eq1682 (σ x)
       grind)
    | exact resolve eq1682 eq2106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2106
  have eq2478 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2477
  have eq2621 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2271 eq609
    | exact resolve eq609 eq2271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq2636 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1914 eq2621
    | exact resolve eq2621 eq1914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1914 eq2621
  have eq2637 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2636
  have eq3277 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2273 eq888
    | (have j0 := eq888 (σ y)
       grind)
    | exact resolve eq888 eq2273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888 eq2273
  have eq3285 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq3277
    | exact resolve eq3277 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3277
  have eq3286 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3285
  have eq3296 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2637 eq3286
    | exact resolve eq3286 eq2637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2637 eq3286
  have eq3303 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3296 eq27
    | exact resolve eq27 eq3296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3296
  have eq3337 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2251 eq3303
    | (have r₁ := eq3303
       have r₂ := eq2251
       grind)
    | exact resolve eq3303 eq2251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2251 eq3303
  have eq3338 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3337
  have eq3339 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3338
  have eq3340 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2132 eq3339
    | exact resolve eq3339 eq2132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2132 eq3339
  have eq3341 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq3340
  have eq3790 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3341 eq181
    | (have r₁ := eq181
       have r₂ := eq3341
       grind)
    | exact resolve eq181 eq3341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq3799 : (σ y) = (k (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3341 eq695
    | exact resolve eq695 eq3341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq3808 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3341 eq940
    | exact resolve eq940 eq3341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940 eq3341
  have eq3813 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq3790
  have eq3821 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3808 eq3799
    | exact resolve eq3799 eq3808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3799
  have eq3827 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3808 eq3813
    | exact resolve eq3813 eq3808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3813
  have eq3832 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3808 eq3821
    | exact resolve eq3821 eq3808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3808 eq3821
  have eq3833 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq3832
  have eq3835 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3827 eq3833
    | exact resolve eq3833 eq3827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3827 eq3833
  have eq3836 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq3835
  have eq3840 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3836 eq31
    | exact resolve eq31 eq3836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq3882 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq3836 eq2271
    | exact resolve eq2271 eq3836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2271 eq3836
  have eq3885 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3882
  have eq3894 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2478 eq3885
    | exact resolve eq3885 eq2478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2478 eq3885
  have eq3895 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq3894
  have eq3912 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq3840
    | exact resolve eq3840 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3840
  have eq3922 : (M.op x y) ≠ (M.op x y) ∨ (k y (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq180
       have i₂ := eq3912
       grind)
    | exact superpose eq3912 eq180
    | (have r₁ := eq180
       have r₂ := eq3912
       grind)
    | exact resolve eq180 eq3912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq3927 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq936
       have i₂ := eq3912
       grind)
    | exact superpose eq3912 eq936
    | exact resolve eq936 eq3912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq3933 : (k y (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by grind
  clear eq3922
  have eq3937 : (M.op x y) = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq3927 eq3933
    | exact resolve eq3933 eq3927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3933
  have eq4089 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3895 eq141
    | exact resolve eq141 eq3895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq3895
  have eq4107 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq4089
    | exact resolve eq4089 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4089
  have eq4424 : y = (k y (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq3927 eq699
    | exact resolve eq699 eq3927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699 eq3927
  have eq4459 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq3937 eq4424
    | exact resolve eq4424 eq3937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3937 eq4424
  have eq4460 : y = (M.op x y) ∨ x = y := by grind
  clear eq4459
  have eq4498 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq4460
  have eq4499 : x = y := by
    first
    | (have r₁ := eq4498
       have r₂ := eq3912
       grind)
    | exact resolve eq4498 eq3912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3912 eq4498
  have eq4506 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4499
       grind)
    | exact superpose eq4499 eq18
    | exact resolve eq18 eq4499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4507 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq4499
       grind)
    | exact superpose eq4499 eq24
    | exact resolve eq24 eq4499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq4520 : (M.op x y) = (k x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq607
       have i₂ := eq4499
       grind)
    | exact superpose eq4499 eq607
    | exact resolve eq607 eq4499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607 eq4499
  have eq4548 : x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4107 eq4520
    | exact resolve eq4520 eq4107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4107 eq4520
  have eq4549 : x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq4548
  have eq4552 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq4507
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4507
    | exact resolve eq4507 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4507
  have eq4554 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4549
       have i₂ := eq4506
       grind)
    | exact superpose eq4506 eq4549
    | exact resolve eq4549 eq4506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4549
  have eq4555 : x = (M.op x y) := by grind
  clear eq4554
  have eq4556 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4552 eq26
    | exact resolve eq26 eq4552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4552
  have eq4760 : x = (k x (M.op x y)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq1682 x
       have i₂ := eq4506
       grind)
    | exact superpose eq4506 eq1682
    | (have j0 := eq1682 x
       grind)
    | exact resolve eq1682 eq4506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1682 eq4506
  have eq4765 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq4760
       have i₂ := eq4555
       grind)
    | exact superpose eq4555 eq4760
    | exact resolve eq4760 eq4555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4760
  have eq4774 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq4765
       have i₂ := eq4555
       grind)
    | exact superpose eq4555 eq4765
    | exact resolve eq4765 eq4555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4765
  have eq4775 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq4774
  have eq4849 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4556 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq4556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4850 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq4556 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq4556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4556
  have eq4872 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4849
  have eq4876 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq4872
       have r₂ := eq4850
       grind)
    | exact resolve eq4872 eq4850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4850 eq4872
  have eq4979 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq4876 eq97
    | exact resolve eq97 eq4876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq4876
  have eq4998 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq4979
       have i₂ := eq4555
       grind)
    | exact superpose eq4555 eq4979
    | exact resolve eq4979 eq4555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4555 eq4979
  have eq5002 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq4775 eq4998
    | exact resolve eq4998 eq4775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4775 eq4998
  have eq5016 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5002 eq14
    | exact resolve eq14 eq5002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5002
  have eq5017 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq5016
    | exact resolve eq5016 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5016
  have eq5021 : False := by grind
  exact eq5021

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_x_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq50 : x ≠ (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq60 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq84
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq84
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq84 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq84
       grind)
    | exact superpose eq84 eq16
    | exact resolve eq16 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq95
    | exact resolve eq95 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq97 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
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
  have eq101 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq149 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq127 eq16
    | exact resolve eq16 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq203 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq56 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq56
    | (have j0 := eq56 y
       grind)
    | exact resolve eq56 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq214 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq57
    | (have j0 := eq57 (σ y)
       grind)
    | exact resolve eq57 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq514 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq58 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq525 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq514 X0
       grind)
    | exact superpose eq514 eq14
    | exact resolve eq14 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq1001 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq59 eq525
    | exact resolve eq525 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq1003 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq60 eq525
    | exact resolve eq525 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq525
  have eq1020 : x ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq1001 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq1053 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1003 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8154 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8155 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8154
    | exact resolve eq8154 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8154
  have eq8166 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8155
       have r₂ := eq27
       grind)
    | exact resolve eq8155 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8155
  have eq8168 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8166
    | exact resolve eq8166 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8166
  have eq8170 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8168
    | exact resolve eq8168 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8168
  have eq8358 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8170 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq8170
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq8170
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq8170
       grind)
    | exact resolve eq12 eq8170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8170
  have eq8389 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8358
       have r₂ := eq26
       grind)
    | exact resolve eq8358 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8358
  have eq8391 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8389
    | exact resolve eq8389 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8389
  have eq8392 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq8391
  have eq8676 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8392 eq98
    | exact resolve eq98 eq8392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq8392
  have eq8684 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8676
  have eq8686 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8684
       have r₂ := eq27
       grind)
    | exact resolve eq8684 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8684
  have eq8689 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq8686
       grind)
    | exact superpose eq8686 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq8686
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq8686
       grind)
    | exact resolve eq12 eq8686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8686
  have eq8722 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8689
       have r₂ := eq18
       grind)
    | exact resolve eq8689 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8689
  have eq8724 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8722
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8722
    | exact resolve eq8722 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8722
  have eq8725 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8724
  have eq9216 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq84
       have i₂ := eq8725
       grind)
    | exact superpose eq8725 eq84
    | exact resolve eq84 eq8725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8725
  have eq9230 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq9216
    | exact resolve eq9216 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9216
  have eq9285 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9230 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq9230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9288 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq9285
    | exact resolve eq9285 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9285
  have eq9299 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq9288
       have r₂ := eq27
       grind)
    | exact resolve eq9288 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9288
  have eq9301 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq9299
    | exact resolve eq9299 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9299
  have eq9303 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq9301
    | exact resolve eq9301 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9301
  have eq9304 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9303
  have eq9533 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9304 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq9304
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq9304
       grind)
    | exact resolve eq12 eq9304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9304
  have eq9572 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9533
       have r₂ := eq26
       grind)
    | exact resolve eq9533 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9533
  have eq9574 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq9572
    | exact resolve eq9572 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9572
  have eq9575 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9574
  have eq9836 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9575 eq9230
    | exact resolve eq9230 eq9575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9230 eq9575
  have eq9838 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9836
  have eq9842 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9838
       have r₂ := eq27
       grind)
    | exact resolve eq9838 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9838
  have eq9845 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9842 eq51
    | (have r₁ := eq51
       have r₂ := eq9842
       grind)
    | exact resolve eq51 eq9842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq9848 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9842 eq214
    | exact resolve eq214 eq9842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq9874 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9842 eq1003
    | exact resolve eq1003 eq9842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003
  have eq9875 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9842 eq1053
    | (have r₁ := eq1053
       have r₂ := eq9842
       grind)
    | exact resolve eq1053 eq9842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053
  have eq9877 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq9875
  have eq9878 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq9845
  have eq10132 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9877 eq49
    | exact resolve eq49 eq9877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq9877
  have eq10148 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq10132
    | exact resolve eq10132 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10132
  have eq10158 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9878 eq94
    | exact resolve eq94 eq9878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq9878
  have eq10185 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq10158
    | exact resolve eq10158 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10158
  have eq10190 : y = (k y x) := by
    first
    | (have r₁ := eq10185
       have r₂ := eq50
       grind)
    | exact resolve eq10185 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq10185
  have eq10196 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq84
       have i₂ := eq10190
       grind)
    | exact superpose eq10190 eq84
    | exact resolve eq84 eq10190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10190
  have eq10212 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq10196
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10196
    | exact resolve eq10196 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10196
  have eq10490 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq101 x
       have i₂ := eq10148
       grind)
    | exact superpose eq10148 eq101
    | (have j0 := eq101 x
       grind)
    | exact resolve eq101 eq10148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10148
  have eq10491 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq10490
  have eq10669 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9874 eq9848
    | exact resolve eq9848 eq9874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9848 eq9874
  have eq10711 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10669
  have eq10714 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq10711
    | exact resolve eq10711 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10711
  have eq10755 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10714 eq9842
    | exact resolve eq9842 eq10714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9842 eq10714
  have eq10760 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq10755
  have eq10776 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10760 eq29
    | exact resolve eq29 eq10760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq10760
  have eq10922 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq10776
    | exact resolve eq10776 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq10776
  have eq10935 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq10922 eq20
    | exact resolve eq20 eq10922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11019 : x ≠ x ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq10922 eq1020
    | (have r₁ := eq1020
       have r₂ := eq10922
       grind)
    | exact resolve eq1020 eq10922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq11021 : x = (k x x) ∨ x = y := by grind
  clear eq11019
  have eq11088 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq10935
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10935
    | exact resolve eq10935 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10935
  have eq11589 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq43
       have i₂ := eq11021
       grind)
    | exact superpose eq11021 eq43
    | exact resolve eq43 eq11021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11021
  have eq11608 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq11589
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11589
    | exact resolve eq11589 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11589
  have eq12057 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq11088 eq11608
    | exact resolve eq11608 eq11088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11088 eq11608
  have eq12073 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq12057
  have eq12711 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq12073 eq149
    | exact resolve eq149 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq12073
  have eq12727 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq30 eq12711
    | exact resolve eq12711 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq12711
  have eq13160 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq12727 eq101
    | (have j0 := eq101 (M.op x y)
       grind)
    | exact resolve eq101 eq12727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12727
  have eq13161 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by grind
  clear eq13160
  have eq13514 : y = (M.op (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq13161 eq203
    | exact resolve eq203 eq13161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203 eq13161
  have eq13807 : y = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq10922 eq13514
    | exact resolve eq13514 eq10922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13514
  have eq13851 : y = (M.op x y) ∨ x = y := by grind
  clear eq13807
  have eq13853 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13851
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13851
    | exact resolve eq13851 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13851
  have eq13946 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq13853 eq10922
    | exact resolve eq10922 eq13853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10922 eq13853
  have eq13959 : x = y := by grind
  clear eq13946
  have eq14029 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq13959
       grind)
    | exact superpose eq13959 eq18
    | exact resolve eq18 eq13959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq14030 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq13959
       grind)
    | exact superpose eq13959 eq24
    | exact resolve eq24 eq13959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq14038 : (σ (k x x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq84
       have i₂ := eq13959
       grind)
    | exact superpose eq13959 eq84
    | exact resolve eq84 eq13959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq13959
  have eq14156 : (σ y) = (σ (k x x)) := by
    first
    | exact superpose eq10212 eq14038
    | exact resolve eq14038 eq10212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10212 eq14038
  have eq14163 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq14030
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14030
    | exact resolve eq14030 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14030
  have eq14171 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq14156
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq14156
    | exact resolve eq14156 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq14156
  have eq14499 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq14163 eq26
    | exact resolve eq26 eq14163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq14672 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10491
       have i₂ := eq14029
       grind)
    | exact superpose eq14029 eq10491
    | exact resolve eq10491 eq14029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10491 eq14029
  have eq14741 : x = (M.op x y) := by grind
  clear eq14672
  have eq15197 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq14741 eq20
    | exact resolve eq20 eq14741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq14741
  have eq15369 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq15197
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15197
    | exact resolve eq15197 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq15197
  have eq15716 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq15369 eq14171
    | exact resolve eq14171 eq15369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14171
  have eq15717 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq14163 eq15716
    | exact resolve eq15716 eq14163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14163 eq15716
  have eq15718 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq15369 eq15717
    | exact resolve eq15717 eq15369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15717
  have eq15727 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq15718 eq101
    | (have j0 := eq101 (σ (M.op x y))
       grind)
    | exact resolve eq101 eq15718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq15718
  have eq15728 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq15727
  have eq15753 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq15369 eq14499
    | exact resolve eq14499 eq15369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14499 eq15369
  have eq15846 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15728 eq15753
    | exact resolve eq15753 eq15728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15728 eq15753
  have eq15847 : False := by grind
  exact eq15847

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then Y else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_y_pyx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq26 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
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
  have eq32 : ∀ X0 X1 X2 : G, (k (τ X2) (k (τ X0) X1)) = (τ (k X2 (k X0 (σ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq22
    | exact resolve eq22 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 (k (τ X0) X1) X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq28
    | exact resolve eq28 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X0 X0) X0 X2
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq61
    | exact resolve eq61 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq75
    | exact resolve eq75 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 (M.op X1 X0) X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq76
    | exact resolve eq76 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq225 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0) X0
       have i₂ := eq225 (σ X0)
       grind)
    | exact superpose eq225 eq22
    | (have j1 := eq225 (σ X0)
       grind)
    | exact resolve eq22 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq240 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq239 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq239
    | (have j0 := eq239 X0
       grind)
    | exact resolve eq239 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq281 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X1) X0) X5)) X1) = X1 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq61 X1 (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X0 X5
       have i₂ := eq62 X3 X2 X4 X0
       grind)
    | exact superpose eq62 eq61
    | exact resolve eq61 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq62
  have eq517 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq73 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq591 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2508 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq591 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq591 X0 X1
       grind)
    | exact superpose eq591 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq591 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq591 X0 X1
       grind)
    | exact resolve eq12 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2509 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq591 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq591 X0 X1
       grind)
    | exact superpose eq591 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq591 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq591 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq591 X0 X1
       grind)
    | exact resolve eq13 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2541 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq591 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq2543 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2509 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2509
  have eq2549 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2541 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2541
  have eq2556 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2543 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2543
    | (have j0 := eq2543 X0 X1
       grind)
    | exact resolve eq2543 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2543
  have eq2557 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2556 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2556
  have eq2558 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2508 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq2508 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq2508 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2508
  have eq2575 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2558 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2558
    | (have j0 := eq2558 X0 X1
       grind)
    | exact resolve eq2558 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2558
  have eq2583 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2557 X1 X0
       have j1 := eq2549 X1 X0
       grind)
    | (have r₁ := eq2557 X0 X1
       have r₂ := eq2549 X0 X1
       grind)
    | (have r₁ := eq2557 X0 X0
       have r₂ := eq2549 X0 X0
       grind)
    | exact resolve eq2557 eq2549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2549 eq2557
  have eq2589 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2583 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq2583
    | (have j0 := eq2583 (τ X1) (τ X0)
       grind)
    | exact resolve eq2583 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2607 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq2583 X1 X0
       grind)
    | exact superpose eq2583 eq10
    | (have j1 := eq2583 X1 X0
       grind)
    | exact resolve eq10 eq2583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2630 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2589 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2589
    | (have j0 := eq2589 X0 X1
       grind)
    | exact resolve eq2589 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2589
  have eq2647 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2630 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2630
    | (have j0 := eq2630 X0 X1
       grind)
    | exact resolve eq2630 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2630
  have eq2652 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2647 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2647
    | (have j0 := eq2647 X0 X1
       grind)
    | exact resolve eq2647 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2647
  have eq2657 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2652 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2652
    | (have j0 := eq2652 X0 X1
       grind)
    | exact resolve eq2652 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2652
  have eq2662 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2657 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2657
    | (have j0 := eq2657 X0 X1
       grind)
    | exact resolve eq2657 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2657
  have eq2673 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2583 X1 X0
       have i₂ := eq2662 X0 X1
       grind)
    | exact superpose eq2662 eq2583
    | (have j0 := eq2583 X1 X0
       have j1 := eq2662 (σ X0) (σ X1)
       grind)
    | exact resolve eq2583 eq2662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2674 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq2662 X0 (σ X1)
       grind)
    | exact superpose eq2662 eq22
    | (have j1 := eq2662 X0 (σ X1)
       grind)
    | exact resolve eq22 eq2662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2685 : ∀ X0 X1 X2 : G, (τ (k X2 (k X0 (σ X1)))) = (k (τ X2) (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 X0 X1 X2
       have i₂ := eq2662 (τ X0) X1
       grind)
    | exact superpose eq2662 eq32
    | (have j1 := eq2662 (τ X0) X1
       grind)
    | exact resolve eq32 eq2662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2766 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) ∨ (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2674 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq68 (σ X0)
       grind)
    | exact superpose eq68 eq2674
    | (have j0 := eq2674 (M.op (σ X0) (σ X0)) X0
       grind)
    | exact resolve eq2674 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq2674
  have eq2862 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 ∨ (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2766 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2766
    | (have j0 := eq2766 X0
       grind)
    | exact resolve eq2766 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2766
  have eq2880 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2862 X0
       have i₂ := eq90 (σ X0) (σ X0)
       grind)
    | exact superpose eq90 eq2862
    | (have j0 := eq2862 X0
       grind)
    | exact resolve eq2862 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2862
  have eq2881 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | exact superpose eq240 eq2880
    | (have j0 := eq2880 X0
       have j1 := eq240 X0
       grind)
    | exact resolve eq2880 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240 eq2880
  have eq2894 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ X0)) X1) = X1 ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq75 (σ X0) X1
       have i₂ := eq2881 X0
       grind)
    | exact superpose eq2881 eq75
    | (have j1 := eq2881 X0
       grind)
    | exact resolve eq75 eq2881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2928 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) (σ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq107 (σ X0) (σ X0)
       have i₂ := eq2881 X0
       grind)
    | exact superpose eq2881 eq107
    | (have j1 := eq2881 X0
       grind)
    | (have r₁ := eq107 (σ X0) (σ X0)
       have r₂ := eq2881 X0
       grind)
    | exact resolve eq107 eq2881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2936 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) (M.op (σ X0) X1)) (σ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq517 (σ X0) (σ X0) x
       have i₂ := eq2881 X0
       grind)
    | exact superpose eq2881 eq517
    | (have j1 := eq2881 X0
       grind)
    | exact resolve eq517 eq2881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2881
  have eq2940 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2928 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2928
  have eq2943 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (σ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2936 X0 X1
       have i₂ := eq90 (σ X0) X1
       grind)
    | exact superpose eq90 eq2936
    | (have j0 := eq2936 X0 X1
       grind)
    | exact resolve eq2936 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2936
  have eq2946 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2940 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq2940
    | (have j0 := eq2940 X0
       grind)
    | exact resolve eq2940 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2940
  have eq2974 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq27 (τ X0) X0 (τ X0)
       have i₂ := eq2946 (τ X0)
       grind)
    | exact superpose eq2946 eq27
    | (have j1 := eq2946 (τ X0)
       grind)
    | exact resolve eq27 eq2946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2946
  have eq2997 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2974 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2974
    | (have j0 := eq2974 X0
       grind)
    | exact resolve eq2974 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2974
  have eq3014 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ X0))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2997 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq2997
    | (have j0 := eq2997 X0
       grind)
    | exact resolve eq2997 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2997
  have eq3029 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3014 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3014
    | (have j0 := eq3014 X0
       grind)
    | exact resolve eq3014 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3014
  have eq3045 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f3045_14 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (k X0 X0) = X0 := by
      intro X0
      grind
    have f3045_15 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
      intro X0 X1
      grind
    have f3045_24 : X0 ≠ (k (M.op X0 X0) X0) := by grind
    have f3045_26 : X0 ≠ (M.op X0 X0) := by grind
    have f3045_51 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
      intro X0
      first
      | (have i₁ := f3045_14 x
         have i₂ := f3045_15 x x
         grind)
      | exact superpose f3045_15 f3045_14
      | (have j1 := f3045_15 X0 X0
         grind)
      | exact resolve f3045_14 f3045_15
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f3045_57 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
      intro X0
      first
      | (have j0 := f3045_51 X0
         grind)
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f3045_114 : X0 ≠ X0 ∨ X0 = (M.op X0 X0) := by
      first
      | (have i₁ := f3045_24
         have i₂ := f3045_57 X0
         grind)
      | exact superpose f3045_57 f3045_24
      | (have j1 := f3045_57 X0
         grind)
      | (have r₁ := f3045_24
         have r₂ := f3045_57 X0
         grind)
      | exact resolve f3045_24 f3045_57
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f3045_119 : X0 = (M.op X0 X0) := by grind
    have f3045_122 : False := by
      first
      | (have r₁ := f3045_119
         have r₂ := f3045_26
         grind)
      | exact resolve f3045_119 f3045_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f3045_122
  clear eq3029
  have eq3065 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3045 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3045
  have eq3082 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3065 X0
       have j1 := eq107 X0 X0
       grind)
    | (have r₁ := eq3065 x
       have r₂ := eq107 x x
       grind)
    | exact resolve eq3065 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq3065
  have eq3111 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2583 X0 (M.op X0 X0)
       have i₂ := eq3082 X0
       grind)
    | exact superpose eq3082 eq2583
    | (have j0 := eq2583 X0 (M.op X0 X0)
       grind)
    | exact resolve eq2583 eq3082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3082
  have eq4015 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ (τ X0) = (k (k (τ X0) (τ X0)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2943 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2943
    | (have j0 := eq2943 (τ X0) X1
       grind)
    | exact resolve eq2943 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4106 : ∀ X0 X1 : G, (τ X0) = (τ (k (k X0 (σ (τ X0))) X0)) ∨ (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4015 X0 X1
       have i₂ := eq40 X0 (τ X0) X0
       grind)
    | exact superpose eq40 eq4015
    | (have j0 := eq4015 X0 X1
       grind)
    | exact resolve eq4015 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq4015
  have eq4108 : ∀ X0 X1 : G, (τ X0) = (τ (k (k X0 X0) X0)) ∨ (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4106 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4106
    | (have j0 := eq4106 X0 X1
       grind)
    | exact resolve eq4106 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4106
  have eq4117 : ∀ X0 X1 : G, (σ (τ X0)) = (k (k X0 X0) X0) ∨ (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k (k X0 X0) X0)
       have i₂ := eq4108 X0 X1
       grind)
    | exact superpose eq4108 eq11
    | (have j1 := eq4108 X0 X1
       grind)
    | exact resolve eq11 eq4108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4108
  have eq4163 : ∀ X0 X1 : G, (k (k X0 X0) X0) = X0 ∨ (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4117 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4117
    | (have j0 := eq4117 X0 X1
       grind)
    | exact resolve eq4117 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4117
  have eq4492 : ∀ X0 X1 : G, (k (k X0 X0) X0) = X0 ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq2943 eq2894
    | (have j0 := eq2894 X0 X1
       have j1 := eq2943 X0 X1
       grind)
    | exact resolve eq2894 eq2943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2894
  have eq4493 : ∀ X0 X1 : G, (k (k X0 X0) X0) = X0 ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | exact superpose eq4492 eq2943
    | (have j0 := eq2943 X0 X1
       have j1 := eq4492 X0 X1
       grind)
    | exact resolve eq2943 eq4492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2943
  have eq4501 : ∀ X0 X1 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) (σ (τ X0))) ∨ (M.op (σ (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27 (τ X0) X0 (τ X0)
       have i₂ := eq4492 (τ X0) X1
       grind)
    | exact superpose eq4492 eq27
    | (have j1 := eq4492 (τ X0) X1
       grind)
    | exact resolve eq27 eq4492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4492
  have eq4524 : ∀ X0 X1 : G, (k (k X0 X0) X0) = X0 ∨ (M.op (σ (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4501 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4501
    | (have j0 := eq4501 X0 X1
       grind)
    | exact resolve eq4501 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4501
  have eq4541 : ∀ X0 X1 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4524 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4524
    | (have j0 := eq4524 X0 X1
       grind)
    | exact resolve eq4524 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4524
  have eq4706 : ∀ X0 X1 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq4541 eq4163
    | (have j0 := eq4163 X0 X1
       have j1 := eq4541 X0 X1
       grind)
    | exact resolve eq4163 eq4541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4163 eq4541
  have eq4761 : ∀ X0 X1 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4706 X0 X1
       have i₂ := eq2662 (k X0 X0) X0
       grind)
    | exact superpose eq2662 eq4706
    | (have j0 := eq4706 X0 (k X0 X0)
       have j1 := eq2662 (k X0 X0) X0
       grind)
    | exact resolve eq4706 eq2662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4706
  have eq4869 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (σ (σ X0)) = (M.op X1 (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (k (σ X0) (σ X0)) X0
       have i₂ := eq4493 (σ X0) X1
       grind)
    | exact superpose eq4493 eq22
    | (have j1 := eq4493 (σ X0) X1
       grind)
    | exact resolve eq22 eq4493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4493
  have eq4884 : ∀ X0 X1 : G, (τ (σ X0)) = (k (k (τ (σ X0)) X0) X0) ∨ (σ (σ X0)) = (M.op X1 (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4869 X0 X1
       have i₂ := eq22 (σ X0) X0
       grind)
    | exact superpose eq22 eq4869
    | (have j0 := eq4869 X0 X1
       grind)
    | exact resolve eq4869 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4869
  have eq4901 : ∀ X0 X1 : G, (σ (σ X0)) = (M.op X1 (σ (σ X0))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4884 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4884
    | (have j0 := eq4884 X0 X1
       grind)
    | exact resolve eq4884 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4884
  have eq9819 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq4761 X0 (k X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4761
  have eq9820 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq9819 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9819
  have eq9830 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9820 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq9820
    | exact resolve eq9820 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11352 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have j0 := eq9830 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9830
  have eq15829 : ∀ X0 X1 : G, (M.op (σ X1) X0) ≠ X0 ∨ (σ (k X1 (τ X0))) = X0 ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2575 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2575
    | exact resolve eq2575 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15842 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ X0)) ∨ (σ (σ X0)) = (σ (k X1 (σ X0))) ∨ (σ (σ X0)) = (σ (k X1 (σ X0))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2575 X0 (σ X0)
       have i₂ := eq4901 X0 (σ X0)
       grind)
    | exact superpose eq4901 eq2575
    | (have j0 := eq2575 X1 (σ X0)
       have j1 := eq4901 X0 X1
       grind)
    | (have r₁ := eq2575 X0 (σ X0)
       have r₂ := eq4901 X0 (σ X0)
       grind)
    | exact resolve eq2575 eq4901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2575 eq4901
  have eq15846 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ X0)) ∨ (σ (σ X0)) = (σ (k X1 (σ X0))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq15842 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15842
  have eq15847 : ∀ X0 X1 : G, (σ (σ X0)) = (σ (k X1 (σ X0))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq15846 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15846
  have eq15852 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (M.op (σ X1) X0) ≠ X0 ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15829 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15829
    | (have j0 := eq15829 X0 X1
       grind)
    | exact resolve eq15829 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15829
  have eq15858 : ∀ X0 X1 : G, (M.op (σ X1) X0) ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15852 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15852
    | (have j0 := eq15852 X0 X1
       grind)
    | exact resolve eq15852 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15852
  have eq15890 : ∀ X0 X1 : G, (k X1 (σ X0)) = (τ (σ (σ X0))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 (σ X0))
       have i₂ := eq15847 X0 X1
       grind)
    | exact superpose eq15847 eq10
    | (have j1 := eq15847 X0 X1
       grind)
    | exact resolve eq10 eq15847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15847
  have eq16020 : ∀ X0 X1 : G, (k (k X0 X0) X0) = X0 ∨ (σ X0) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15890 X0 X1
       have i₂ := eq10 (σ X0)
       grind)
    | exact superpose eq10 eq15890
    | (have j0 := eq15890 X0 X1
       grind)
    | exact resolve eq15890 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15890
  have eq16051 : ∀ X0 X1 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) (σ (τ X0))) ∨ (σ (τ X0)) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq27 (τ X0) X0 (τ X0)
       have i₂ := eq16020 (τ X0) X1
       grind)
    | exact superpose eq16020 eq27
    | (have j1 := eq16020 (τ X0) (k (σ (τ X0)) X0)
       grind)
    | exact resolve eq27 eq16020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq16020
  have eq16112 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have j0 := eq11352 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11352
  have eq16123 : ∀ X0 X1 : G, (k (k X0 X0) X0) = X0 ∨ (σ (τ X0)) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16051 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16051
    | (have j0 := eq16051 X0 X1
       grind)
    | exact resolve eq16051 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16051
  have eq16164 : ∀ X0 X1 : G, (k (k X0 X0) X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16123 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16123
    | (have j0 := eq16123 X0 X1
       grind)
    | exact resolve eq16123 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16123
  have eq16252 : ∀ X0 : G, X0 ≠ X0 ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq16164 X0 (k X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16164
  have eq16253 : ∀ X0 : G, (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq16252 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16252
  have eq20316 : ∀ X0 X1 : G, (M.op (σ X0) X1) ≠ (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = (k (σ X0) (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = (k (σ X0) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15858 (M.op (σ X1) X1) X1
       have i₂ := eq90 (σ X1) X1
       grind)
    | exact superpose eq90 eq15858
    | (have j0 := eq15858 (M.op (σ X0) X1) X0
       grind)
    | (have r₁ := eq15858 (M.op (σ X1) X1) X1
       have r₂ := eq90 (σ X1) X1
       grind)
    | exact resolve eq15858 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15858
  have eq20320 : ∀ X0 X1 : G, (M.op (σ X0) X1) ≠ (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = (k (σ X0) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq20316 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20316
  have eq20321 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (k (σ X0) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq20320 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20320
  have eq20337 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20321 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20321
    | exact resolve eq20321 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20355 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (k X0 (τ (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op (σ X0) X1)
       have i₂ := eq20321 X0 X1
       grind)
    | exact superpose eq20321 eq28
    | exact resolve eq28 eq20321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20321
  have eq20384 : ∀ X0 X1 : G, (k (M.op (M.op (M.op X1 X1) X0) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20337 (M.op (M.op (M.op X0 X0) X1) X0) X1
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq20337
    | exact resolve eq20337 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20406 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20337 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq20337
    | exact resolve eq20337 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20674 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op (M.op (M.op X1 X1) (σ X0)) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op (M.op (M.op X1 X1) (σ X0)) X1) X0
       have i₂ := eq20384 (σ X0) X1
       grind)
    | exact superpose eq20384 eq22
    | exact resolve eq22 eq20384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20384
  have eq20724 : ∀ X0 X1 : G, (k (τ (M.op (M.op (M.op X1 X1) (σ X0)) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20674 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20674
    | exact resolve eq20674 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20674
  have eq20880 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (M.op (M.op X1 (σ X0)) (M.op X1 X2))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (M.op (M.op X1 (σ X0)) (M.op X1 X2)) X0
       have i₂ := eq20406 (σ X0) X1 X2
       grind)
    | exact superpose eq20406 eq22
    | exact resolve eq22 eq20406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20899 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (σ (M.op (M.op X1 (τ X0)) (M.op X1 X2))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (M.op (M.op X1 (τ X0)) (M.op X1 X2))
       have i₂ := eq20406 (τ X0) X1 X2
       grind)
    | exact superpose eq20406 eq18
    | exact resolve eq18 eq20406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20406
  have eq20912 : ∀ X0 X1 X2 : G, (k (σ (M.op (M.op X1 (τ X0)) (M.op X1 X2))) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20899 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20899
    | exact resolve eq20899 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20899
  have eq20930 : ∀ X0 X1 X2 : G, (k (τ (M.op (M.op X1 (σ X0)) (M.op X1 X2))) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20880 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20880
    | exact resolve eq20880 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20880
  have eq21505 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20355 X0 (σ X1)
       have i₂ := eq2607 X0 X1
       grind)
    | exact superpose eq2607 eq20355
    | (have j1 := eq2607 X0 X1
       grind)
    | exact resolve eq20355 eq2607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2607
  have eq22572 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (τ (M.op (M.op (M.op X1 X1) (σ (σ X0))) X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (τ (M.op (M.op (M.op X1 X1) (σ (σ X0))) X1)) X0
       have i₂ := eq20724 (σ X0) X1
       grind)
    | exact superpose eq20724 eq22
    | exact resolve eq22 eq20724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20724
  have eq22623 : ∀ X0 X1 : G, (k (τ (τ (M.op (M.op (M.op X1 X1) (σ (σ X0))) X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22572 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22572
    | exact resolve eq22572 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22572
  have eq22875 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (σ (σ (M.op (M.op X1 (τ (τ X0))) (M.op X1 X2)))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (σ (M.op (M.op X1 (τ (τ X0))) (M.op X1 X2)))
       have i₂ := eq20912 (τ X0) X1 X2
       grind)
    | exact superpose eq20912 eq18
    | exact resolve eq18 eq20912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20912
  have eq22888 : ∀ X0 X1 X2 : G, (k (σ (σ (M.op (M.op X1 (τ (τ X0))) (M.op X1 X2)))) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22875 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22875
    | exact resolve eq22875 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22875
  have eq23167 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (τ (M.op (M.op X1 (σ (σ X0))) (M.op X1 X2)))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (τ (M.op (M.op X1 (σ (σ X0))) (M.op X1 X2))) X0
       have i₂ := eq20930 (σ X0) X1 X2
       grind)
    | exact superpose eq20930 eq22
    | exact resolve eq22 eq20930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20930
  have eq23218 : ∀ X0 X1 X2 : G, (k (τ (τ (M.op (M.op X1 (σ (σ X0))) (M.op X1 X2)))) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23167 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23167
    | exact resolve eq23167 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23167
  have eq28638 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (k X0 (τ (k (σ X0) X1))) ∨ (σ X1) = (M.op (σ X1) (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (k (σ X0) X1)
       have i₂ := eq21505 (σ X0) X1
       grind)
    | exact superpose eq21505 eq28
    | (have j1 := eq21505 (σ X0) X1
       grind)
    | exact resolve eq28 eq21505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21505
  have eq28697 : ∀ X0 X1 : G, (k X0 (τ X1)) = (k X0 (k X0 (τ X1))) ∨ (σ X1) = (M.op (σ X1) (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq28638 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq28638
    | (have j0 := eq28638 X0 X1
       grind)
    | exact resolve eq28638 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28638
  have eq49472 : ∀ X0 X1 : G, (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (k X1 X0) = (k X1 (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28697 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq28697
    | (have j0 := eq28697 X1 (σ X0)
       grind)
    | exact resolve eq28697 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28697
  have eq51130 : ∀ X0 X1 X2 : G, (k (τ (τ (M.op (σ (σ X0)) (M.op (σ (σ X0)) X2)))) X1) = X1 ∨ (k X1 X0) = (k X1 (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23218 X1 (σ (σ X0)) X2
       have i₂ := eq49472 X0 X1
       grind)
    | exact superpose eq49472 eq23218
    | (have j1 := eq49472 X0 X1
       grind)
    | exact resolve eq23218 eq49472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23218
  have eq51210 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ (σ X0)) X1) (σ (σ X0))) X1) = X1 ∨ (k X2 X0) = (k X2 (k X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (σ (σ X0)) (σ (σ X2))
       have i₂ := eq49472 X0 X2
       grind)
    | exact superpose eq49472 eq9
    | (have j1 := eq49472 X0 X2
       grind)
    | exact resolve eq9 eq49472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51211 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ X0)) ∨ (σ (σ X0)) = (k (σ (σ X1)) (σ (σ X0))) ∨ (k X1 X0) = (k X1 (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ (σ X1)) (σ (σ X0))
       have i₂ := eq49472 X0 X1
       grind)
    | exact superpose eq49472 eq12
    | (have j0 := eq12 (σ (σ X1)) (σ (σ X0))
       have j1 := eq49472 X0 X1
       grind)
    | (have r₁ := eq12 (σ (σ X1)) (σ (σ X0))
       have r₂ := eq49472 X0 X1
       grind)
    | exact resolve eq12 eq49472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51261 : ∀ X0 X1 X2 : G, (σ (σ X0)) = (M.op (M.op (σ (σ X0)) (M.op (σ (σ X0)) X2)) (σ (σ X0))) ∨ (k X1 X0) = (k X1 (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq517 (σ (σ X0)) (σ (σ X1)) X2
       have i₂ := eq49472 X0 X1
       grind)
    | exact superpose eq49472 eq517
    | (have j1 := eq49472 X0 X1
       grind)
    | exact resolve eq517 eq49472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49472
  have eq51369 : ∀ X0 X1 : G, (σ (σ X0)) = (k (σ (σ X1)) (σ (σ X0))) ∨ (k X1 X0) = (k X1 (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq51211 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51211
  have eq51427 : ∀ X0 X1 X2 : G, (σ (σ X0)) = (M.op (M.op (σ (σ X0)) X2) (σ (σ X0))) ∨ (k X1 X0) = (k X1 (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51261 X0 X1 X2
       have i₂ := eq90 (σ (σ X0)) X2
       grind)
    | exact superpose eq90 eq51261
    | (have j0 := eq51261 X0 X1 X2
       grind)
    | exact resolve eq51261 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51261
  have eq51450 : ∀ X0 X1 : G, (σ (σ X0)) = (σ (k (σ X1) (σ X0))) ∨ (k X1 X0) = (k X1 (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq51369 X0 X1
       have i₂ := eq15 (σ X1) (σ X0)
       grind)
    | exact superpose eq15 eq51369
    | (have j0 := eq51369 X0 X1
       grind)
    | exact resolve eq51369 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51369
  have eq51478 : ∀ X0 X1 X2 : G, (k (τ (τ (M.op (σ (σ X0)) X2))) X1) = X1 ∨ (k X1 X0) = (k X1 (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51130 X0 X1 X2
       have i₂ := eq90 (σ (σ X0)) X2
       grind)
    | exact superpose eq90 eq51130
    | (have j0 := eq51130 X0 X1 X2
       grind)
    | exact resolve eq51130 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51130
  have eq51511 : ∀ X0 X1 : G, (k X1 X0) = (k X1 (k X1 X0)) ∨ (σ (σ X0)) = (σ (σ (k X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq51450 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq51450
    | (have j0 := eq51450 X0 X1
       grind)
    | exact resolve eq51450 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51450
  have eq52465 : ∀ X0 X1 : G, (τ (k X0 X1)) = (k (τ X0) (τ (k X0 X1))) ∨ (σ (σ (τ X1))) = (σ (σ (τ (k X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51511 (τ X0) (τ X1)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq51511
    | exact resolve eq51511 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51511
  have eq52586 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (k X0 (k X0 X1))) ∨ (σ (σ (τ X1))) = (σ (σ (τ (k X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq52465 X0 X1
       have i₂ := eq31 (k X0 X1) X0
       grind)
    | exact superpose eq31 eq52465
    | (have j0 := eq52465 X0 X1
       grind)
    | exact resolve eq52465 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52465
  have eq52631 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (σ (τ X1))) ∨ (τ (k X0 X1)) = (τ (k X0 (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq52586 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq52586
    | (have j0 := eq52586 X0 X1
       grind)
    | exact resolve eq52586 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52586
  have eq52654 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (k X0 (k X0 X1))) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52631 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq52631
    | (have j0 := eq52631 X0 X1
       grind)
    | exact resolve eq52631 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52631
  have eq53664 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (k X0 (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 (k X0 X1))
       have i₂ := eq52654 X0 X1
       grind)
    | exact superpose eq52654 eq11
    | (have j1 := eq52654 X0 X1
       grind)
    | exact resolve eq11 eq52654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52654
  have eq53760 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53664 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq53664
    | (have j0 := eq53664 X0 X1
       grind)
    | exact resolve eq53664 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53664
  have eq53870 : ∀ X0 X1 : G, (τ (k X0 X1)) = (k (τ X0) (τ (k X0 X1))) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq53760 (τ X1) (τ X0)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq53760
    | exact resolve eq53760 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53760
  have eq53993 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (k X0 (k X0 X1))) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq53870 X0 X1
       have i₂ := eq31 (k X0 X1) X0
       grind)
    | exact superpose eq31 eq53870
    | (have j0 := eq53870 X0 X1
       grind)
    | exact resolve eq53870 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53870
  have eq54038 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ X1)) ∨ (τ (k X0 X1)) = (τ (k X0 (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq53993 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq53993
    | (have j0 := eq53993 X0 X1
       grind)
    | exact resolve eq53993 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53993
  have eq54061 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (k X0 (k X0 X1))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq54038 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq54038
    | (have j0 := eq54038 X0 X1
       grind)
    | exact resolve eq54038 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54038
  have eq54112 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (k X0 (k X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 (k X0 X1))
       have i₂ := eq54061 X0 X1
       grind)
    | exact superpose eq54061 eq11
    | (have j1 := eq54061 X0 X1
       grind)
    | exact resolve eq11 eq54061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54061
  have eq54208 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (k X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq54112 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq54112
    | (have j0 := eq54112 X0 (k X0 X1)
       grind)
    | exact resolve eq54112 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54112
  have eq54362 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ (k (τ X0) X1))) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (k (τ X0) X1)
       have i₂ := eq54208 (τ X0) X1
       grind)
    | exact superpose eq54208 eq17
    | (have j1 := eq54208 X0 (σ (k (τ X0) X1))
       grind)
    | exact resolve eq17 eq54208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54208
  have eq54391 : ∀ X0 X1 : G, (k X0 (σ X1)) = (k X0 (k X0 (σ X1))) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq54362 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq54362
    | (have j0 := eq54362 X0 X1
       grind)
    | exact resolve eq54362 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54362
  have eq61235 : ∀ X0 X1 X2 : G, (k X2 (τ X0)) = (k X2 (k X2 (τ X0))) ∨ (k (τ (τ (M.op (σ X0) X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51478 (τ X0) X2 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq51478
    | (have j0 := eq51478 (τ X0) X2 X2
       grind)
    | exact resolve eq51478 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51478
  have eq77634 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (k (τ X0) (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2685 X0 X1 X0
       have i₂ := eq54391 X0 X1
       grind)
    | exact superpose eq54391 eq2685
    | (have j0 := eq2685 X0 X1 x
       have j1 := eq54391 X0 X1
       grind)
    | exact resolve eq2685 eq54391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2685 eq54391
  have eq78121 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (k (τ X0) (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq77634 X0 X1
       have j1 := eq12 (τ X0) X1
       grind)
    | (have r₁ := eq77634 X0 X1
       have r₂ := eq12 (τ X0) X1
       grind)
    | exact resolve eq77634 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77634
  have eq78449 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq78121 X0 X1
       have i₂ := eq20337 (τ X0) X1
       grind)
    | exact superpose eq20337 eq78121
    | (have j0 := eq78121 X0 X1
       grind)
    | exact resolve eq78121 eq20337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20337 eq78121
  have eq78579 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq78449 X0 X1
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq78449
    | (have j0 := eq78449 X0 X1
       grind)
    | exact resolve eq78449 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq78449
  have eq78728 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq78579 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq78579
    | exact resolve eq78579 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78579
  have eq79390 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq78728 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78728
  have eq120588 : ∀ X0 X1 X2 : G, (σ (k (τ X0) (τ X1))) = (k X0 (σ (k (τ X0) (τ X1)))) ∨ (τ X0) = (k (τ (τ (M.op (σ X1) X2))) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (k (τ X0) (τ X1))
       have i₂ := eq61235 X1 X2 (τ X0)
       grind)
    | exact superpose eq61235 eq17
    | (have j1 := eq61235 X1 X2 (τ X0)
       grind)
    | exact resolve eq17 eq61235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61235
  have eq120619 : ∀ X0 X1 X2 : G, (k X0 (σ (τ X1))) = (k X0 (k X0 (σ (τ X1)))) ∨ (τ X0) = (k (τ (τ (M.op (σ X1) X2))) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq120588 X0 X1 X2
       have i₂ := eq17 X0 (τ X1)
       grind)
    | exact superpose eq17 eq120588
    | (have j0 := eq120588 X0 X1 X2
       grind)
    | exact resolve eq120588 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120588
  have eq120663 : ∀ X0 X1 X2 : G, (k X0 X1) = (k X0 (k X0 X1)) ∨ (τ X0) = (k (τ (τ (M.op (σ X1) X2))) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq120619 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq120619
    | (have j0 := eq120619 X0 X1 X2
       grind)
    | exact resolve eq120619 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120619
  have eq120696 : ∀ X0 X1 X2 : G, (τ X0) = (τ (k (τ (M.op (σ X1) X2)) X0)) ∨ (k X0 X1) = (k X0 (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq120663 X0 X1 X2
       have i₂ := eq31 X0 (τ (M.op (σ X1) X2))
       grind)
    | exact superpose eq31 eq120663
    | (have j0 := eq120663 X0 X1 X2
       grind)
    | exact resolve eq120663 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120663
  have eq120780 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (τ (M.op (σ X1) X2)) X0) ∨ (k X0 X1) = (k X0 (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k (τ (M.op (σ X1) X2)) X0)
       have i₂ := eq120696 X0 X1 X2
       grind)
    | exact superpose eq120696 eq11
    | (have j1 := eq120696 X0 X1 X2
       grind)
    | exact resolve eq11 eq120696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120696
  have eq120953 : ∀ X0 X1 X2 : G, (k (τ (M.op (σ X1) X2)) X0) = X0 ∨ (k X0 X1) = (k X0 (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq120780 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq120780
    | (have j0 := eq120780 X0 X1 X2
       grind)
    | exact resolve eq120780 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120780
  have eq121117 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (σ (τ (M.op (σ X1) X2))) X0) ∨ (k (τ X0) X1) = (k (τ X0) (k (τ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (τ (M.op (σ X1) X2))
       have i₂ := eq120953 (τ X0) X1 X2
       grind)
    | exact superpose eq120953 eq18
    | (have j1 := eq120953 (τ X0) X1 X2
       grind)
    | exact resolve eq18 eq120953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120953
  have eq121173 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (M.op (σ X1) X2) X0) ∨ (k (τ X0) X1) = (k (τ X0) (k (τ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq121117 X0 X1 X2
       have i₂ := eq11 (M.op (σ X1) X2)
       grind)
    | exact superpose eq11 eq121117
    | (have j0 := eq121117 X0 X1 X2
       grind)
    | exact resolve eq121117 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121117
  have eq121240 : ∀ X0 X1 X2 : G, (k (M.op (σ X1) X2) X0) = X0 ∨ (k (τ X0) X1) = (k (τ X0) (k (τ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq121173 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq121173
    | (have j0 := eq121173 X0 X1 X2
       grind)
    | exact resolve eq121173 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121173
  have eq121269 : ∀ X0 X1 X2 : G, (k (τ X0) X1) = (τ (k X0 (k X0 (σ X1)))) ∨ (k (M.op (σ X1) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq121240 X0 X1 X2
       have i₂ := eq32 X0 X1 X0
       grind)
    | exact superpose eq32 eq121240
    | (have j0 := eq121240 X0 X1 X2
       grind)
    | exact resolve eq121240 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq121240
  have eq122432 : ∀ X0 X1 X2 : G, (k (τ X1) (τ X0)) = (τ (k X1 (k X1 X0))) ∨ (k (M.op X0 X2) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq121269 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq121269
    | exact resolve eq121269 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121269
  have eq122922 : ∀ X0 X1 X2 : G, (τ (k X1 X0)) = (τ (k X1 (k X1 X0))) ∨ (k (M.op X0 X2) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq122432 X0 X1 X2
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq122432
    | (have j0 := eq122432 X0 X1 X2
       grind)
    | exact resolve eq122432 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122432
  have eq123288 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k X0 (k X0 X1)) ∨ (k (M.op X1 X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X0 (k X0 X1))
       have i₂ := eq122922 X1 X0 X2
       grind)
    | exact superpose eq122922 eq11
    | (have j1 := eq122922 X1 X0 X2
       grind)
    | exact resolve eq11 eq122922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122922
  have eq123455 : ∀ X0 X1 X2 : G, (k X0 X1) = (k X0 (k X0 X1)) ∨ (k (M.op X1 X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq123288 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq123288
    | (have j0 := eq123288 X0 X1 X2
       grind)
    | exact resolve eq123288 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123288
  have eq124060 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X1)) = (k X0 (σ (k (τ X0) X1))) ∨ (τ X0) = (k (M.op X1 X2) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (k (τ X0) X1)
       have i₂ := eq123455 (τ X0) X1 X2
       grind)
    | exact superpose eq123455 eq17
    | (have j1 := eq123455 (τ X0) X1 X2
       grind)
    | exact resolve eq17 eq123455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123455
  have eq124095 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (k X0 (k X0 (σ X1))) ∨ (τ X0) = (k (M.op X1 X2) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq124060 X0 X1 X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq124060
    | (have j0 := eq124060 X0 X1 X2
       grind)
    | exact resolve eq124060 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124060
  have eq125754 : ∀ X0 X1 X2 : G, (τ X1) = (k (M.op (τ X0) X2) (τ X1)) ∨ (k X1 X0) = (k X1 (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq124095 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq124095
    | (have j0 := eq124095 X1 (τ X0) X2
       grind)
    | exact resolve eq124095 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124095
  have eq192443 : ∀ X0 X1 X2 : G, (k X2 X0) = (k X2 (k X2 X0)) ∨ (M.op (σ (σ X0)) X1) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq51427 eq51210
    | (have j0 := eq51210 X0 X1 X2
       have j1 := eq51427 X0 X2 X2
       grind)
    | exact resolve eq51210 eq51427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51210
  have eq192994 : ∀ X0 X1 X2 : G, (k X1 X0) = (k X1 (k X1 X0)) ∨ (σ (σ X0)) = (M.op X2 (σ (σ X0))) := by
    intro X0 X1 X2
    first
    | exact superpose eq192443 eq51427
    | (have j0 := eq51427 X0 X1 X2
       have j1 := eq192443 X0 X1 X1
       grind)
    | exact resolve eq51427 eq192443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51427
  have eq193236 : ∀ X0 X1 X2 : G, (τ (k X0 X1)) = (k (τ X0) (τ (k X0 X1))) ∨ (M.op (σ (σ (τ X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq192443 (τ X0) X1 (τ X1)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq192443
    | (have j0 := eq192443 (τ X1) X2 X2
       grind)
    | exact resolve eq192443 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193383 : ∀ X0 X1 X2 : G, (τ (k (σ X0) X1)) = (k X0 (τ (k (σ X0) X1))) ∨ (M.op (σ (σ X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X0 (k (σ X0) X1)
       have i₂ := eq192443 X1 X2 (σ X0)
       grind)
    | exact superpose eq192443 eq28
    | (have j1 := eq192443 X1 X2 X2
       grind)
    | exact resolve eq28 eq192443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192443
  have eq193475 : ∀ X0 X1 X2 : G, (k X0 (τ X1)) = (k X0 (k X0 (τ X1))) ∨ (M.op (σ (σ X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq193383 X0 X1 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq193383
    | (have j0 := eq193383 X0 X1 X2
       grind)
    | exact resolve eq193383 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193383
  have eq193508 : ∀ X0 X1 X2 : G, (τ (k X0 X1)) = (τ (k X0 (k X0 X1))) ∨ (M.op (σ (σ (τ X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq193236 X0 X1 X2
       have i₂ := eq31 (k X0 X1) X0
       grind)
    | exact superpose eq31 eq193236
    | (have j0 := eq193236 X0 X1 X2
       grind)
    | exact resolve eq193236 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193236
  have eq193563 : ∀ X0 X1 X2 : G, (τ (k X0 X1)) = (τ (k X0 (k X0 X1))) ∨ (M.op (σ X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq193508 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq193508
    | (have j0 := eq193508 X0 X1 X2
       grind)
    | exact resolve eq193508 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193508
  have eq197714 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k X0 (k X0 X1)) ∨ (M.op (σ X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X0 (k X0 X1))
       have i₂ := eq193563 X0 X1 X2
       grind)
    | exact superpose eq193563 eq11
    | (have j1 := eq193563 X0 X1 X2
       grind)
    | exact resolve eq11 eq193563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193563
  have eq197905 : ∀ X0 X1 X2 : G, (k X0 X1) = (k X0 (k X0 X1)) ∨ (M.op (σ X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq197714 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq197714
    | (have j0 := eq197714 X0 X1 X2
       grind)
    | exact resolve eq197714 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197714
  have eq198510 : ∀ X0 X1 X2 : G, (τ (k X0 X1)) = (k (τ X0) (τ (k X0 X1))) ∨ (M.op (σ (τ X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq197905 (τ X1) (τ X0) X2
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq197905
    | (have j0 := eq197905 X0 (τ X1) X2
       grind)
    | exact resolve eq197905 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197905
  have eq198784 : ∀ X0 X1 X2 : G, (τ (k X0 X1)) = (τ (k X0 (k X0 X1))) ∨ (M.op (σ (τ X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq198510 X0 X1 X2
       have i₂ := eq31 (k X0 X1) X0
       grind)
    | exact superpose eq31 eq198510
    | (have j0 := eq198510 X0 X1 X2
       grind)
    | exact resolve eq198510 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq198510
  have eq198839 : ∀ X0 X1 X2 : G, (τ (k X0 X1)) = (τ (k X0 (k X0 X1))) ∨ (M.op X1 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq198784 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq198784
    | (have j0 := eq198784 X0 X1 X2
       grind)
    | exact resolve eq198784 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198784
  have eq200460 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k X0 (k X0 X1)) ∨ (M.op X1 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X0 (k X0 X1))
       have i₂ := eq198839 X0 X1 X2
       grind)
    | exact superpose eq198839 eq11
    | (have j1 := eq198839 X0 X1 X2
       grind)
    | exact resolve eq11 eq198839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198839
  have eq200650 : ∀ X0 X1 X2 : G, (k X0 X1) = (k X0 (k X0 X1)) ∨ (M.op X1 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq200460 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq200460
    | (have j0 := eq200460 X0 X1 X2
       grind)
    | exact resolve eq200460 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200460
  have eq201390 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X1)) = (k X0 (σ (k (τ X0) X1))) ∨ (M.op X1 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (k (τ X0) X1)
       have i₂ := eq200650 (τ X0) X1 X2
       grind)
    | exact superpose eq200650 eq17
    | (have j1 := eq200650 X0 X1 X2
       grind)
    | exact resolve eq17 eq200650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200650
  have eq201431 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (k X0 (k X0 (σ X1))) ∨ (M.op X1 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq201390 X0 X1 X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq201390
    | (have j0 := eq201390 X0 X1 X2
       grind)
    | exact resolve eq201390 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq201390
  have eq204799 : ∀ X0 X1 X2 : G, (k X1 X0) = (k X1 (k X1 X0)) ∨ (M.op (τ X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq201431 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq201431
    | (have j0 := eq201431 X0 (τ X0) X2
       grind)
    | exact resolve eq201431 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201431
  have eq205356 : ∀ X0 X1 X2 : G, (k X1 X0) = (k X1 (k X1 X0)) ∨ (τ X1) = (k X2 (τ X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq204799 eq125754
    | (have j0 := eq125754 X0 X1 X2
       have j1 := eq204799 X0 X1 X2
       grind)
    | exact resolve eq125754 eq204799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125754 eq204799
  have eq207864 : ∀ X0 X1 X2 : G, (σ (k X0 (τ X1))) = (k (σ X0) (k (σ X0) X1)) ∨ (τ X0) = (k X2 (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X0 X1 X0
       have i₂ := eq205356 (τ X1) X0 X2
       grind)
    | exact superpose eq205356 eq26
    | (have j1 := eq205356 X0 X0 X2
       grind)
    | exact resolve eq26 eq205356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205356
  have eq208029 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (k (σ X0) (k (σ X0) X1)) ∨ (τ X0) = (k X2 (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq207864 X0 X1 X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq207864
    | (have j0 := eq207864 X0 X1 X2
       grind)
    | exact resolve eq207864 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207864
  have eq220145 : ∀ X0 X1 X2 : G, (τ (k (σ X0) X1)) = (k X0 (τ (k (σ X0) X1))) ∨ (σ (σ X1)) = (M.op X2 (σ (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X0 (k (σ X0) X1)
       have i₂ := eq192994 X1 (σ X0) X2
       grind)
    | exact superpose eq192994 eq28
    | (have j1 := eq192994 X1 X1 X2
       grind)
    | exact resolve eq28 eq192994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192994
  have eq220235 : ∀ X0 X1 X2 : G, (k X0 (τ X1)) = (k X0 (k X0 (τ X1))) ∨ (σ (σ X1)) = (M.op X2 (σ (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq220145 X0 X1 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq220145
    | (have j0 := eq220145 X0 X1 X2
       grind)
    | exact resolve eq220145 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq220145
  have eq220351 : ∀ X0 X1 X2 : G, (k X1 X0) = (k X1 (k X1 X0)) ∨ (M.op (σ (σ (σ X0))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq193475 X0 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq193475
    | (have j0 := eq193475 X0 (σ X0) X2
       grind)
    | exact resolve eq193475 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193475
  have eq249043 : ∀ X0 X1 X2 : G, (k X0 X1) = (k X0 (k X0 X1)) ∨ (τ (τ X0)) = (k X2 (τ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq208029 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq208029
    | (have j0 := eq208029 (τ X0) X1 X2
       grind)
    | exact resolve eq208029 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208029
  have eq249857 : ∀ X0 X1 X2 : G, (σ (k X0 (τ X1))) = (k (σ X0) (k (σ X0) X1)) ∨ (τ (τ X0)) = (k X2 (τ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X0 X1 X0
       have i₂ := eq249043 X0 (τ X1) X2
       grind)
    | exact superpose eq249043 eq26
    | (have j1 := eq249043 X0 X1 X2
       grind)
    | exact resolve eq26 eq249043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq249043
  have eq250045 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (k (σ X0) (k (σ X0) X1)) ∨ (τ (τ X0)) = (k X2 (τ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq249857 X0 X1 X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq249857
    | (have j0 := eq249857 X0 X1 X2
       grind)
    | exact resolve eq249857 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq249857
  have eq254689 : ∀ X0 X1 X2 : G, (σ (σ (σ X0))) = (M.op X2 (σ (σ (σ X0)))) ∨ (k X1 X0) = (k X1 (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq220235 X0 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq220235
    | (have j0 := eq220235 X0 (σ X0) X2
       grind)
    | exact resolve eq220235 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220235
  have eq259056 : ∀ X0 X1 X5 X6 : G, (M.op (M.op X1 (M.op (σ (σ (σ X0))) X5)) X1) = X1 ∨ (k X6 X0) = (k X6 (k X6 X0)) := by
    intro X0 X1 X5 X6
    first
    | (have i₁ := eq281 (σ (σ (σ X0))) X1 x x x X5
       have i₂ := eq254689 X0 X6 (M.op (M.op (M.op (M.op (M.op x x) (M.op x x)) (σ (σ (σ X0)))) x) X1)
       grind)
    | exact superpose eq254689 eq281
    | (have j1 := eq254689 X0 X6 x
       grind)
    | exact resolve eq281 eq254689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq254689
  have eq259377 : ∀ X0 X1 X5 X6 : G, (k X6 X0) = (k X6 (k X6 X0)) ∨ (M.op (M.op X1 X5) X1) = X1 := by
    intro X0 X1 X5 X6
    first
    | exact superpose eq220351 eq259056
    | (have j0 := eq259056 X0 X1 X5 X6
       have j1 := eq220351 X0 X6 x
       grind)
    | exact resolve eq259056 eq220351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220351 eq259056
  have eq300794 : ∀ X0 X1 X2 : G, (τ (τ (τ X0))) = (k X2 (τ (τ (τ X0)))) ∨ (k X0 X1) = (k X0 (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq250045 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq250045
    | (have j0 := eq250045 (τ X0) X1 X2
       grind)
    | exact resolve eq250045 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250045
  have eq301401 : ∀ X0 X1 : G, (σ (τ (τ (τ X0)))) = (M.op (σ (τ (τ (τ X0)))) (σ (τ (τ (τ X0))))) ∨ (σ (τ (τ (τ X0)))) = (M.op (σ (τ (τ (τ X0)))) (σ (τ (τ (τ X0))))) ∨ (k X0 X1) = (k X0 (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16112 (τ (τ (τ X0)))
       have i₂ := eq300794 X0 X1 (τ (τ (τ X0)))
       grind)
    | exact superpose eq300794 eq16112
    | (have j1 := eq300794 X0 X1 x
       grind)
    | exact resolve eq16112 eq300794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16112 eq300794
  have eq301547 : ∀ X0 X1 : G, (σ (τ (τ (τ X0)))) = (M.op (σ (τ (τ (τ X0)))) (σ (τ (τ (τ X0))))) ∨ (k X0 X1) = (k X0 (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq301401 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301401
  have eq301592 : ∀ X0 X1 : G, (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) ∨ (k X0 X1) = (k X0 (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq301547 X0 X1
       have i₂ := eq11 (τ (τ X0))
       grind)
    | exact superpose eq11 eq301547
    | (have j0 := eq301547 X0 X1
       grind)
    | exact resolve eq301547 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301547
  have eq305714 : ∀ X0 X1 X2 : G, (k (σ (σ (M.op (M.op (τ (τ X0)) (τ (τ X1))) (τ (τ X0))))) X1) = X1 ∨ (k X0 X2) = (k X0 (k X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22888 X1 (τ (τ X0)) (τ (τ X0))
       have i₂ := eq301592 X0 X2
       grind)
    | exact superpose eq301592 eq22888
    | (have j1 := eq301592 X0 X2
       grind)
    | exact resolve eq22888 eq301592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22888 eq301592
  have eq305890 : ∀ X0 X1 X2 : G, (k (σ (σ (τ (τ X0)))) X1) = X1 ∨ (k X0 X2) = (k X0 (k X0 X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq259377 eq305714
    | (have j0 := eq305714 X0 X1 X2
       have j1 := eq259377 X2 X1 x X0
       grind)
    | exact resolve eq305714 eq259377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259377 eq305714
  have eq305994 : ∀ X0 X1 X2 : G, (k (σ (τ X0)) X1) = X1 ∨ (k X0 X2) = (k X0 (k X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq305890 X0 X1 X2
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq305890
    | (have j0 := eq305890 X0 X1 X2
       grind)
    | exact resolve eq305890 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305890
  have eq306031 : ∀ X0 X1 X2 : G, (k X0 X2) = (k X0 (k X0 X2)) ∨ (k X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq305994 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq305994
    | (have j0 := eq305994 X0 X1 X2
       grind)
    | exact resolve eq305994 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305994
  have eq306612 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X0 X1) ∨ (k X0 X1) = (k X0 (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq306031 X0 (k X0 X1) X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306031
  have eq306613 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq306612 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306612
  have eq307023 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X0) ∨ (k X0 X1) = (M.op X0 (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq306613 X0 X1
       have i₂ := eq2662 X0 (k X0 X1)
       grind)
    | exact superpose eq2662 eq306613
    | (have j1 := eq2662 X0 (k X0 X1)
       grind)
    | exact resolve eq306613 eq2662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306613
  have eq308416 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X1) (M.op (k X0 X1) X2)) X0) = X0 ∨ (k X0 X1) = (M.op X0 (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 (k X0 X1) X2
       have i₂ := eq307023 X0 X1
       grind)
    | exact superpose eq307023 eq9
    | (have j1 := eq307023 X0 X1
       grind)
    | exact resolve eq9 eq307023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307023
  have eq308903 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 (k X0 X1)) ∨ (M.op (M.op (k X0 X1) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq308416 X0 X1 X2
       have i₂ := eq90 (k X0 X1) X2
       grind)
    | exact superpose eq90 eq308416
    | (have j0 := eq308416 X0 X1 X2
       grind)
    | exact resolve eq308416 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308416
  have eq314553 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X0 X1) (k X0 X0)) ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq308903 (k X0 X0) X0 x
       have i₂ := eq16253 X0
       grind)
    | exact superpose eq16253 eq308903
    | exact resolve eq308903 eq16253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16253 eq308903
  have eq315849 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (M.op (k X0 X0) (M.op X0 (k X0 X0))) ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq113 (k X0 X0) X0
       have i₂ := eq314553 X0 (k X0 X0)
       grind)
    | exact superpose eq314553 eq113
    | (have j1 := eq314553 X0 x
       grind)
    | exact resolve eq113 eq314553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314553
  have eq316651 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | exact superpose eq9820 eq315849
    | (have j0 := eq315849 X0
       have j1 := eq9820 X0
       grind)
    | exact resolve eq315849 eq9820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9820 eq315849
  have eq316652 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq316651 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316651
  have eq316914 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq316652 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq316652
    | exact resolve eq316652 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316652
  have eq317333 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq316914 X0
       have i₂ := eq2662 X0 X0
       grind)
    | exact superpose eq2662 eq316914
    | (have j1 := eq2662 X0 X0
       grind)
    | exact resolve eq316914 eq2662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317334 : ∀ X0 : G, (σ (σ X0)) = (M.op (σ (σ (k X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq316914 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq316914
    | exact resolve eq316914 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316914
  have eq322933 : ∀ X0 : G, (σ (σ (σ X0))) = (M.op (σ (σ (σ (k X0 X0)))) (σ (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq317334 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq317334
    | exact resolve eq317334 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317334
  have eq330217 : ∀ X0 : G, (σ (σ (σ X0))) = (M.op (σ (σ (σ (k X0 X0)))) (σ (σ (σ X0)))) := by
    intro X0
    first
    | (have j0 := eq322933 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322933
  have eq333477 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq317333 eq3111
    | (have j0 := eq3111 X0
       have j1 := eq317333 X0
       grind)
    | exact resolve eq3111 eq317333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3111 eq317333
  have eq348459 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (σ (σ (k X0 X0)))) X1) (σ (σ (σ X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ (σ (σ (k X0 X0)))) (σ (σ (σ X0)))
       have i₂ := eq330217 X0
       grind)
    | exact superpose eq330217 eq9
    | exact resolve eq9 eq330217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330217
  have eq419364 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2673 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2673
  have eq420163 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq419364 x y
       grind)
    | exact superpose eq419364 eq16
    | (have j1 := eq419364 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq419364 x y
       grind)
    | exact resolve eq16 eq419364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419364
  have eq420711 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq420163
  have eq421070 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq420711
       grind)
    | exact superpose eq420711 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq420711
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq420711
       grind)
    | exact resolve eq12 eq420711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420711
  have eq421366 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq421070
  have eq421517 : (σ y) = (σ (k x y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq421366
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq421366
    | exact resolve eq421366 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421366
  have eq421580 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2662 eq421517
    | (have j1 := eq2662 x y
       grind)
    | exact resolve eq421517 eq2662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421517
  have eq422539 : (M.op x y) = (τ (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq421580
       grind)
    | exact superpose eq421580 eq10
    | exact resolve eq10 eq421580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421580
  have eq422907 : y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq422539
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq422539
    | exact resolve eq422539 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422539
  have eq422908 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq422907
       grind)
    | exact superpose eq422907 eq9
    | exact resolve eq9 eq422907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq422910 : y ≠ y ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq422907
       grind)
    | exact superpose eq422907 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq422907
       grind)
    | exact resolve eq12 eq422907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423206 : y = (k x y) ∨ y = (M.op x y) := by grind
  clear eq422910
  have eq423351 : y = (k x y) := by
    first
    | (have j1 := eq79390 x y
       grind)
    | (have r₁ := eq423206
       have r₂ := eq79390 x y
       grind)
    | exact resolve eq423206 eq79390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79390 eq423206
  have eq423352 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq422908 X0
       have i₂ := eq90 y X0
       grind)
    | exact superpose eq90 eq422908
    | exact resolve eq422908 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422908
  have eq423372 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2583 y x
       have i₂ := eq423351
       grind)
    | exact superpose eq423351 eq2583
    | (have j0 := eq2583 y x
       grind)
    | exact resolve eq2583 eq423351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2583 eq423351
  have eq425626 : (M.op y x) = (M.op x (M.op y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq113 x y
       have i₂ := eq423352 x
       grind)
    | exact superpose eq423352 eq113
    | exact resolve eq113 eq423352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq423352
  have eq426192 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq422907 eq425626
    | exact resolve eq425626 eq422907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422907 eq425626
  have eq426193 : y = (M.op x y) := by grind
  clear eq426192
  have eq426360 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq426193
       grind)
    | exact superpose eq426193 eq16
    | exact resolve eq16 eq426193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426193
  have eq436985 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq426360
       have r₂ := eq423372
       grind)
    | exact resolve eq426360 eq423372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423372
  have eq436997 : (τ (σ y)) = (k y (τ (σ y))) := by
    first
    | (have i₁ := eq20355 y (σ x)
       have i₂ := eq436985
       grind)
    | exact superpose eq436985 eq20355
    | exact resolve eq20355 eq436985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20355
  have eq437513 : y = (k y y) := by
    first
    | (have i₁ := eq436997
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq436997
    | exact resolve eq436997 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436997
  have eq437803 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2662 y y
       have i₂ := eq437513
       grind)
    | exact superpose eq437513 eq2662
    | (have j0 := eq2662 y y
       grind)
    | exact resolve eq2662 eq437513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2662 eq437513
  have eq437828 : y = (M.op y y) := by grind
  clear eq437803
  have eq438894 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq75 y X0
       have i₂ := eq437828
       grind)
    | exact superpose eq437828 eq75
    | exact resolve eq75 eq437828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq439089 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq517 y y x
       have i₂ := eq437828
       grind)
    | exact superpose eq437828 eq517
    | exact resolve eq517 eq437828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437828
  have eq439446 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq439089 X0
       have i₂ := eq90 y X0
       grind)
    | exact superpose eq90 eq439089
    | exact resolve eq439089 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq439089
  have eq444989 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq438894 X0
       have i₂ := eq439446 X0
       grind)
    | exact superpose eq439446 eq438894
    | exact resolve eq438894 eq439446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438894
  have eq444990 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq439446 X0
       have i₂ := eq444989 X0
       grind)
    | exact superpose eq444989 eq439446
    | exact resolve eq439446 eq444989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439446
  have eq445193 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op y X1) X0) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq517 y X1 X0
       have i₂ := eq444989 X0
       grind)
    | exact superpose eq444989 eq517
    | exact resolve eq517 eq444989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq446310 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq445193 X0 X0
       have i₂ := eq444989 X0
       grind)
    | exact superpose eq444989 eq445193
    | exact resolve eq445193 eq444989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444989 eq445193
  have eq447441 : ∀ X0 : G, (k (τ (τ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq22623 X0 y
       have i₂ := eq444990 (M.op (M.op y y) (σ (σ X0)))
       grind)
    | exact superpose eq444990 eq22623
    | exact resolve eq22623 eq444990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22623
  have eq471424 : ∀ X0 : G, (M.op (M.op (M.op (σ (σ (σ (τ (τ y))))) X0) (σ (σ (σ (τ (τ y)))))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq348459 (τ (τ y)) X0
       have i₂ := eq447441 (τ (τ y))
       grind)
    | exact superpose eq447441 eq348459
    | exact resolve eq348459 eq447441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348459 eq447441
  have eq471563 : ∀ X0 : G, (M.op (σ (σ (σ (τ (τ y))))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq471424 X0
       have i₂ := eq446310 X0 (σ (σ (σ (τ (τ y)))))
       grind)
    | exact superpose eq446310 eq471424
    | exact resolve eq471424 eq446310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446310 eq471424
  have eq471770 : ∀ X0 : G, (M.op (σ (σ (τ y))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq471563 X0
       have i₂ := eq11 (τ y)
       grind)
    | exact superpose eq11 eq471563
    | exact resolve eq471563 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471563
  have eq471847 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq471770 X0
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq471770
    | exact resolve eq471770 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471770
  have eq473136 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq436985
       have i₂ := eq471847 (σ x)
       grind)
    | exact superpose eq471847 eq436985
    | exact resolve eq436985 eq471847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436985 eq471847
  have eq474391 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq426360
       have i₂ := eq473136
       grind)
    | exact superpose eq473136 eq426360
    | exact resolve eq426360 eq473136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426360
  have eq474651 : (σ x) = (M.op (σ (M.op y y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq333477 y
       have i₂ := eq473136
       grind)
    | exact superpose eq473136 eq333477
    | (have j0 := eq333477 x
       grind)
    | exact resolve eq333477 eq473136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333477
  have eq474687 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq474651
       have i₂ := eq444990 y
       grind)
    | exact superpose eq444990 eq474651
    | exact resolve eq474651 eq444990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444990 eq474651
  have eq474835 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq474687
       have i₂ := eq473136
       grind)
    | exact superpose eq473136 eq474687
    | exact resolve eq474687 eq473136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473136 eq474687
  have eq474836 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq474835
  have eq474962 : False := by grind
  exact eq474962
