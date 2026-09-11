import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxy_pxx_pyx_Equation723 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : (M.op x y) = (M.op x y) := by grind
  have eq19 : (M.op x y) = (M.op x y) := by grind
  clear eq18
  have eq20 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq20
  have eq22 : (σ x) = (σ x) := by grind
  have eq23 : (σ x) = (σ x) := by grind
  clear eq22
  have eq24 : (σ y) = (σ y) := by grind
  have eq25 : (σ y) = (σ y) := by grind
  clear eq24
  have eq26 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq26
  have eq28 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq29 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op (M.op x y) y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq14 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq80 : y ≠ (M.op x y) ∨ x = y ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq37 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq37
    | exact resolve eq37 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (k (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq92 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq88
  have eq93 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq92
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq94
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq94
    | exact resolve eq94 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq100
    | exact resolve eq100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq110 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq38 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq38
    | exact resolve eq38 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq663 : ∀ X0 X1 : G, (M.op y (M.op X0 (M.op (M.op x y) y))) = (M.op (M.op X1 (M.op y (M.op X0 (M.op (M.op x y) y)))) (M.op X0 (M.op (M.op x y) y))) := by
    intro X0 X1
    first
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq711 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X0 X2 X0 X1
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq772 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq69 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq797 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq798 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq797
    | exact resolve eq797 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq801 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq798
       have r₂ := eq28
       grind)
    | exact resolve eq798 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq803 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq801
    | exact resolve eq801 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq806 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq803 eq81
    | (have r₁ := eq81
       have r₂ := eq803
       grind)
    | exact resolve eq81 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq808 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq803 eq28
    | exact resolve eq28 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq809 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq806
  have eq810 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq809
  have eq830 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq810 eq102
    | exact resolve eq102 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq810
  have eq834 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq830
  have eq881 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq711 X1 x X3
       have i₂ := eq711 X1 x X0
       grind)
    | exact superpose eq711 eq711
    | exact resolve eq711 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq916 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (σ (M.op x y)) (σ y)))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq834 eq14
    | exact resolve eq14 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq920 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ y) (M.op (σ (M.op x y)) (σ y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq834 eq711
    | exact resolve eq711 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq1591 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X0 (σ y)))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq920 eq916
    | exact resolve eq916 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916 eq920
  have eq1598 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X0 (σ y)))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq1591 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1591
  have eq1799 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq1598
    | (have j0 := eq1598 (σ x)
       grind)
    | exact resolve eq1598 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1598
  have eq1875 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq803 eq1799
    | exact resolve eq1799 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1799
  have eq1882 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1875
  have eq1883 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq1882
    | exact resolve eq1882 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1882
  have eq1884 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq803 eq1883
    | exact resolve eq1883 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803 eq1883
  have eq1891 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1884
  have eq1897 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1891 eq834
    | exact resolve eq834 eq1891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834 eq1891
  have eq1908 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1897
  have eq1915 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1908
       have r₂ := eq808
       grind)
    | exact resolve eq1908 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808 eq1908
  have eq2000 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq1915 eq30
    | exact resolve eq30 eq1915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1915
  have eq2020 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq2000
    | exact resolve eq2000 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2000
  have eq2021 : y = (M.op x y) ∨ x = y := by grind
  clear eq2020
  have eq2024 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2021 eq21
    | exact resolve eq21 eq2021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2027 : y ≠ y ∨ x = y ∨ (k y x) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq2021 eq80
    | (have r₁ := eq80
       have r₂ := eq2021
       grind)
    | exact resolve eq80 eq2021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq2029 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2021 eq110
    | exact resolve eq110 eq2021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq2040 : y ≠ y ∨ x = y ∨ (k y x) = (M.op y y) := by grind
  clear eq2027
  have eq2041 : (k y x) = (M.op y y) ∨ x = y := by grind
  clear eq2040
  have eq2051 : ∀ X0 : G, (k (σ y) X0) = (k (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2029 X0
       have i₂ := eq84 X0
       grind)
    | exact superpose eq84 eq2029
    | exact resolve eq2029 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq2029
  have eq2054 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2024
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2024
    | exact resolve eq2024 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2024
  have eq2251 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq87
       have i₂ := eq2041
       grind)
    | exact superpose eq2041 eq87
    | exact resolve eq87 eq2041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2041
  have eq2256 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2251
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq2251
    | exact resolve eq2251 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2251
  have eq2773 : (M.op (σ y) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2256 eq2051
    | exact resolve eq2051 eq2256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2051 eq2256
  have eq2775 : (M.op (σ y) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y := by grind
  clear eq2773
  have eq5732 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq772 x y
       have i₂ := eq87
       grind)
    | exact superpose eq87 eq772
    | (have j0 := eq772 x y
       grind)
    | exact resolve eq772 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq772
  have eq5763 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5732
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5732
    | exact resolve eq5732 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5732
  have eq5823 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5763
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5763
    | exact resolve eq5763 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5763
  have eq5878 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5823
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5823
    | exact resolve eq5823 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5823
  have eq5924 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq5878
    | exact resolve eq5878 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5878
  have eq5965 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq5924
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5924
    | exact resolve eq5924 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5924
  have eq5999 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5965
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5965
    | exact resolve eq5965 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5965
  have eq6988 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op y (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq53 eq663
    | exact resolve eq663 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq663
  have eq18351 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq2054 eq5999
    | exact resolve eq5999 eq2054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5999
  have eq18363 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq18351
       have r₂ := eq28
       grind)
    | exact resolve eq18351 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18351
  have eq18366 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2775 eq18363
    | exact resolve eq18363 eq2775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2775 eq18363
  have eq18369 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq18366
  have eq18636 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op y (M.op y y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2021 eq6988
    | exact resolve eq6988 eq2021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6988
  have eq19865 : y = (M.op (M.op x y) (M.op y (M.op y y))) ∨ x = y := by
    first
    | (have i₁ := eq18636 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18636
    | (have j0 := eq18636 x
       grind)
    | exact resolve eq18636 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18636
  have eq19951 : ∀ X0 : G, y = (M.op (M.op x y) (M.op X0 (M.op X0 y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq19865
       have i₂ := eq881 y y X0
       grind)
    | (have i₁ := eq19865
       have i₂ := eq881 X0 y y
       grind)
    | exact superpose eq881 eq19865
    | exact resolve eq19865 eq881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881 eq19865
  have eq20112 : y = (M.op (M.op x y) (M.op x (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq19951 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19951
    | (have j0 := eq19951 x
       grind)
    | exact resolve eq19951 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19951
  have eq20198 : y = (M.op y (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2021 eq20112
    | exact resolve eq20112 eq2021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20112
  have eq20223 : y = (M.op y (M.op x y)) ∨ x = y := by grind
  clear eq20198
  have eq20224 : y = (M.op y (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq20223
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20223
    | exact resolve eq20223 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20223
  have eq20225 : y = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2021 eq20224
    | exact resolve eq20224 eq2021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20224
  have eq20250 : y = (M.op y y) ∨ x = y := by grind
  clear eq20225
  have eq20343 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq93
       have i₂ := eq20250
       grind)
    | exact superpose eq20250 eq93
    | exact resolve eq93 eq20250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq20250
  have eq20415 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq20343
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20343
    | exact resolve eq20343 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20343
  have eq20498 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq20415 eq18369
    | exact resolve eq18369 eq20415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18369 eq20415
  have eq20532 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq20498
  have eq20555 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq20532
       have r₂ := eq2054
       grind)
    | exact resolve eq20532 eq2054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2054 eq20532
  have eq20649 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq20555 eq29
    | exact resolve eq29 eq20555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq20555
  have eq20721 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq20649
    | exact resolve eq20649 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq20649
  have eq20752 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq20721 eq2021
    | exact resolve eq2021 eq20721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2021 eq20721
  have eq20861 : x = y := by grind
  clear eq20752
  have eq20908 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq20861
       grind)
    | exact superpose eq20861 eq19
    | exact resolve eq19 eq20861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq20909 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq20861
       grind)
    | exact superpose eq20861 eq25
    | exact resolve eq25 eq20861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq20861
  have eq20961 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq20909
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20909
    | exact resolve eq20909 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq20909
  have eq20971 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20961 eq27
    | exact resolve eq27 eq20961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq20961
  have eq21127 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20971 eq68
    | exact resolve eq68 eq20971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq20971
  have eq21155 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq21127
       have i₂ := eq20908
       grind)
    | exact superpose eq20908 eq21127
    | exact resolve eq21127 eq20908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20908 eq21127
  have eq21160 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21155 eq15
    | exact resolve eq15 eq21155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21155
  have eq21206 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq21160
    | exact resolve eq21160 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq21160
  have eq21215 : False := by grind
  exact eq21215

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_pxy_pyx_Equation723 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : (M.op x y) = (M.op x y) := by grind
  have eq19 : (M.op x y) = (M.op x y) := by grind
  clear eq18
  have eq20 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq20
  have eq22 : (σ x) = (σ x) := by grind
  have eq23 : (σ x) = (σ x) := by grind
  clear eq22
  have eq24 : (σ y) = (σ y) := by grind
  have eq25 : (σ y) = (σ y) := by grind
  clear eq24
  have eq26 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq26
  have eq28 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq29 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op (M.op x y) y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq14 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq81 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (k (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq92 : (σ (k y y)) = (M.op (σ y) (σ y)) := by grind
  clear eq88
  have eq93 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq92
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
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
  clear eq87
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq94
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq94
    | exact resolve eq94 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq100
    | exact resolve eq100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq117 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq120 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq117
  have eq121 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq120
  have eq127 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq16
    | exact resolve eq16 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq121 eq16
    | exact resolve eq16 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq670 : ∀ X0 : G, (M.op (M.op X0 (M.op (M.op x y) y)) (M.op (M.op x y) y)) = (M.op y (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq711 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X0 X2 X0 X1
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq796 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq797 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq796
    | exact resolve eq796 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796
  have eq800 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq797
       have r₂ := eq28
       grind)
    | exact resolve eq797 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq802 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq800
    | exact resolve eq800 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq805 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq802 eq81
    | (have r₁ := eq81
       have r₂ := eq802
       grind)
    | exact resolve eq81 eq802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq806 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq802 eq54
    | exact resolve eq54 eq802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq808 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq805
  have eq809 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq808
  have eq810 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27 eq806
    | (have j0 := eq806 X0
       grind)
    | exact resolve eq806 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq816 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq809 eq102
    | exact resolve eq102 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq809
  have eq820 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq816
  have eq830 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (M.op (σ (M.op x y)) (σ x)))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq820 eq14
    | exact resolve eq14 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq860 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 x
       have i₂ := eq711 X1 x X0
       grind)
    | exact superpose eq711 eq14
    | exact resolve eq14 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq878 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq802 eq810
    | exact resolve eq810 eq802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802 eq810
  have eq890 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq878 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878
  have eq948 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq820 eq890
    | exact resolve eq890 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq952 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq890 eq56
    | exact resolve eq56 eq890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq959 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq948
  have eq1426 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq820 eq952
    | exact resolve eq952 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820 eq952
  have eq1445 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1426
  have eq1448 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1445 eq830
    | exact resolve eq830 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq1452 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1445 eq890
    | exact resolve eq890 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890 eq1445
  have eq1459 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1452
  have eq1463 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq1448 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448
  have eq1518 : (τ (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1459 eq160
    | exact resolve eq160 eq1459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq1459
  have eq1523 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq1518
    | exact resolve eq1518 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518
  have eq1608 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq959 eq1463
    | exact resolve eq1463 eq959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959 eq1463
  have eq1619 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1608
  have eq1623 : (τ (σ x)) = (M.op y y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1619 eq127
    | exact resolve eq127 eq1619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq1619
  have eq1632 : x = (M.op y y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29 eq1623
    | exact resolve eq1623 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1623
  have eq1636 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq56 y x y
       have i₂ := eq1632
       grind)
    | exact superpose eq1632 eq56
    | exact resolve eq56 eq1632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1639 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1636 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1636
    | (have j0 := eq1636 X0
       grind)
    | exact resolve eq1636 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1636
  have eq1889 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1523 eq1639
    | exact resolve eq1639 eq1523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1523 eq1639
  have eq1896 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1889
  have eq1898 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1632
       have i₂ := eq1896
       grind)
    | exact superpose eq1896 eq1632
    | exact resolve eq1632 eq1896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1632 eq1896
  have eq1904 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1898
  have eq1908 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1904 eq30
    | exact resolve eq30 eq1904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1904
  have eq1928 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1908
    | exact resolve eq1908 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1908
  have eq1929 : x = (M.op x y) ∨ x = y := by grind
  clear eq1928
  have eq2005 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1929 eq21
    | exact resolve eq21 eq1929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2007 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1929 eq53
    | exact resolve eq53 eq1929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq2035 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2007 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2007
    | (have j0 := eq2007 X0
       grind)
    | exact resolve eq2007 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2007
  have eq2037 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq2005
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2005
    | exact resolve eq2005 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2005
  have eq2040 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2037 eq27
    | exact resolve eq27 eq2037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2037
  have eq2701 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op x y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1929 eq670
    | exact resolve eq670 eq1929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670 eq1929
  have eq2717 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op x y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2701 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2701
    | (have j0 := eq2701 X0
       grind)
    | exact resolve eq2701 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2701
  have eq3539 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 (M.op y (M.op x y)))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2717 eq14
    | exact resolve eq14 eq2717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2717
  have eq3975 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2035 eq3539
    | exact resolve eq3539 eq2035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2035 eq3539
  have eq3991 : (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq3975
  have eq4052 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq93
       have i₂ := eq3991
       grind)
    | exact superpose eq3991 eq93
    | exact resolve eq93 eq3991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq3991
  have eq4061 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq4052
    | exact resolve eq4052 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4052
  have eq13811 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op x y)))) ∨ x = y := by
    first
    | exact superpose eq4061 eq860
    | exact resolve eq860 eq4061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4061
  have eq14081 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq13811 eq860
    | exact resolve eq860 eq13811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860 eq13811
  have eq14108 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq14081 eq2040
    | exact resolve eq2040 eq14081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040 eq14081
  have eq14129 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq14108
  have eq14134 : x = y := by
    first
    | (have r₁ := eq14129
       have r₂ := eq28
       grind)
    | exact resolve eq14129 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14129
  have eq14136 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq14134
       grind)
    | exact superpose eq14134 eq19
    | exact resolve eq19 eq14134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq14137 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq14134
       grind)
    | exact superpose eq14134 eq25
    | exact resolve eq25 eq14134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq14134
  have eq14171 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq14137
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14137
    | exact resolve eq14137 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq14137
  have eq14222 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq14171 eq27
    | exact resolve eq27 eq14171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq14171
  have eq14317 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq14222 eq68
    | exact resolve eq68 eq14222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq14222
  have eq14341 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq14317
       have i₂ := eq14136
       grind)
    | exact superpose eq14136 eq14317
    | exact resolve eq14317 eq14136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14136 eq14317
  have eq14343 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14341 eq15
    | exact resolve eq15 eq14341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14341
  have eq14389 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq14343
    | exact resolve eq14343 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq14343
  have eq14398 : False := by grind
  exact eq14398

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_pyy_pyx_Equation723 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : (M.op x y) = (M.op x y) := by grind
  have eq19 : (M.op x y) = (M.op x y) := by grind
  clear eq18
  have eq20 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq20
  have eq22 : (σ x) = (σ x) := by grind
  have eq23 : (σ x) = (σ x) := by grind
  clear eq22
  have eq24 : (σ y) = (σ y) := by grind
  have eq25 : (σ y) = (σ y) := by grind
  clear eq24
  have eq26 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq26
  have eq28 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq29 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op (M.op x y) y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq14 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq81 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (k (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq92 : (σ (k y y)) = (M.op (σ y) (σ y)) := by grind
  clear eq88
  have eq93 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq92
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
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
  clear eq87
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq94
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq94
    | exact resolve eq94 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq100
    | exact resolve eq100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq117 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq120 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq117
  have eq121 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq120
  have eq127 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq16
    | exact resolve eq16 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq121 eq16
    | exact resolve eq16 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq214 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq670 : ∀ X0 : G, (M.op (M.op X0 (M.op (M.op x y) y)) (M.op (M.op x y) y)) = (M.op y (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq711 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X0 X2 X0 X1
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq797 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq798 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq797
    | exact resolve eq797 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq801 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq798
       have r₂ := eq28
       grind)
    | exact resolve eq798 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq803 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq801
    | exact resolve eq801 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq805 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq803 eq214
    | exact resolve eq214 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq806 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq803 eq81
    | (have r₁ := eq81
       have r₂ := eq803
       grind)
    | exact resolve eq81 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq807 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq803 eq54
    | exact resolve eq54 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq809 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq806
  have eq810 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq809
  have eq811 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27 eq807
    | (have j0 := eq807 X0
       grind)
    | exact resolve eq807 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq812 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27 eq805
    | (have j0 := eq805 X0
       grind)
    | exact resolve eq805 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805
  have eq816 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq810 eq102
    | exact resolve eq102 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq810
  have eq820 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq816
  have eq879 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 x
       have i₂ := eq711 X1 x X0
       grind)
    | exact superpose eq711 eq14
    | exact resolve eq14 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq901 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (M.op (σ (M.op x y)) (σ x)))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq820 eq14
    | exact resolve eq14 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1069 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq803 eq811
    | exact resolve eq811 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq1081 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq1069 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069
  have eq1082 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq803 eq812
    | exact resolve eq812 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq1090 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq1082 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082
  have eq1148 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1081 eq56
    | exact resolve eq56 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1218 : ∀ X1 : G, (M.op X1 (M.op X1 (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq1090 eq711
    | exact resolve eq711 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq1090
  have eq1228 : ∀ X1 : G, (M.op X1 (M.op X1 (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq27 eq1218
    | (have j0 := eq1218 X1
       grind)
    | exact resolve eq1218 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218
  have eq1544 : (M.op (σ y) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq820 eq1148
    | exact resolve eq1148 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148
  have eq1563 : (M.op (σ y) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1544
  have eq1570 : (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1563 eq1081
    | exact resolve eq1081 eq1563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1577 : (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1570
  have eq1637 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1577 eq901
    | exact resolve eq901 eq1577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901 eq1577
  have eq1644 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1637
  have eq1645 : (τ (σ x)) = (M.op y y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1644 eq127
    | exact resolve eq127 eq1644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq1644
  have eq1654 : x = (M.op y y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29 eq1645
    | exact resolve eq1645 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645
  have eq1658 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq56 y x y
       have i₂ := eq1654
       grind)
    | exact superpose eq1654 eq56
    | exact resolve eq56 eq1654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1661 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1658 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1658
    | (have j0 := eq1658 X0
       grind)
    | exact resolve eq1658 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1658
  have eq1798 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1228
    | (have j0 := eq1228 (σ x)
       grind)
    | exact resolve eq1228 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228
  have eq1818 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq803 eq1798
    | exact resolve eq1798 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803 eq1798
  have eq1834 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1818
  have eq2070 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1834 eq1563
    | exact resolve eq1563 eq1834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1563 eq1834
  have eq2087 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2070
  have eq2492 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2087 eq820
    | exact resolve eq820 eq2087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820 eq2087
  have eq2507 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2492
  have eq2520 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2507 eq1081
    | exact resolve eq1081 eq2507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081 eq2507
  have eq2527 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2520
  have eq2553 : (τ (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2527 eq160
    | exact resolve eq160 eq2527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq2527
  have eq2559 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq2553
    | exact resolve eq2553 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2553
  have eq2601 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2559 eq1661
    | exact resolve eq1661 eq2559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1661 eq2559
  have eq2609 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2601
  have eq2641 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1654
       have i₂ := eq2609
       grind)
    | exact superpose eq2609 eq1654
    | exact resolve eq1654 eq2609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1654 eq2609
  have eq2648 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq2641
  have eq2654 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2648 eq30
    | exact resolve eq30 eq2648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2648
  have eq2675 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq2654
    | exact resolve eq2654 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2654
  have eq2676 : x = (M.op x y) ∨ x = y := by grind
  clear eq2675
  have eq2680 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2676 eq21
    | exact resolve eq21 eq2676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2682 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2676 eq53
    | exact resolve eq53 eq2676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq2697 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op x y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2676 eq670
    | exact resolve eq670 eq2676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670 eq2676
  have eq2700 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op x y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2697 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2697
    | (have j0 := eq2697 X0
       grind)
    | exact resolve eq2697 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2697
  have eq2714 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2682 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2682
    | (have j0 := eq2682 X0
       grind)
    | exact resolve eq2682 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2682
  have eq2716 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq2680
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2680
    | exact resolve eq2680 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2680
  have eq2742 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2716 eq27
    | exact resolve eq27 eq2716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2716
  have eq3583 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 (M.op y (M.op x y)))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2700 eq14
    | exact resolve eq14 eq2700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2700
  have eq4754 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2714 eq3583
    | exact resolve eq3583 eq2714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2714 eq3583
  have eq4770 : (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq4754
  have eq5099 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq93
       have i₂ := eq4770
       grind)
    | exact superpose eq4770 eq93
    | exact resolve eq93 eq4770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq4770
  have eq5110 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq5099
    | exact resolve eq5099 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5099
  have eq13554 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op x y)))) ∨ x = y := by
    first
    | exact superpose eq5110 eq879
    | exact resolve eq879 eq5110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5110
  have eq13837 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq13554 eq879
    | exact resolve eq879 eq13554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879 eq13554
  have eq13863 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq13837 eq2742
    | exact resolve eq2742 eq13837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2742 eq13837
  have eq13888 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq13863
  have eq13894 : x = y := by
    first
    | (have r₁ := eq13888
       have r₂ := eq28
       grind)
    | exact resolve eq13888 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13888
  have eq13896 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq13894
       grind)
    | exact superpose eq13894 eq19
    | exact resolve eq19 eq13894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq13897 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq13894
       grind)
    | exact superpose eq13894 eq25
    | exact resolve eq25 eq13894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq13894
  have eq13931 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq13897
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq13897
    | exact resolve eq13897 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq13897
  have eq13984 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq13931 eq27
    | exact resolve eq27 eq13931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq13931
  have eq14082 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq13984 eq68
    | exact resolve eq68 eq13984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq13984
  have eq14110 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq14082
       have i₂ := eq13896
       grind)
    | exact superpose eq13896 eq14082
    | exact resolve eq14082 eq13896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13896 eq14082
  have eq14113 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14110 eq15
    | exact resolve eq15 eq14110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14110
  have eq14159 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq14113
    | exact resolve eq14113 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq14113
  have eq14168 : False := by grind
  exact eq14168

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_pxy_pyx_pyy_pxy_Equation731 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
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
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq14 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X1 X1) X0) (M.op X2 X2) X2
       have i₂ := eq14 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k X1 (M.op X1 (M.op (M.op X2 X2) X0))) = (M.op (M.op X1 (M.op (M.op X2 X2) X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 (M.op X1 (M.op (M.op X2 X2) X0))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 (M.op X1 (M.op (M.op X2 X2) X0))
       grind)
    | (have r₁ := eq13 X0 (M.op X0 (M.op (M.op X2 X2) X0))
       have r₂ := eq14 X0 X0 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq79
    | exact resolve eq79 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq84
    | exact resolve eq84 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq88 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq86
    | exact resolve eq86 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq88
    | exact resolve eq88 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq100 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq16
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
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
    | (have r₁ := eq110 x
       have r₂ := eq13 x x
       grind)
    | exact resolve eq110 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq113 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq111 (σ X0)
       grind)
    | exact superpose eq111 eq10
    | exact resolve eq10 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq120 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq113 X0
       have i₂ := eq111 X0
       grind)
    | exact superpose eq111 eq113
    | exact resolve eq113 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq124 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq100
       have i₂ := eq111 sF3
       grind)
    | exact superpose eq111 eq100
    | exact resolve eq100 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq125 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq124
       have i₂ := eq111 y
       grind)
    | exact superpose eq111 eq124
    | exact resolve eq124 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq264 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq111 (τ X0)
       grind)
    | exact superpose eq111 eq34
    | exact resolve eq34 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq16
    | exact resolve eq16 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq275 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq264 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq264
    | exact resolve eq264 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq277 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq275 X0
       have i₂ := eq111 X0
       grind)
    | exact superpose eq111 eq275
    | exact resolve eq275 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq425 : (σ (M.op (k x x) (k x x))) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq120 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq120
    | exact resolve eq120 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq120
  have eq446 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (σ (M.op (k x x) (k x x))) := by
    first
    | (have i₁ := eq425
       have i₂ := eq111 sF2
       grind)
    | exact superpose eq111 eq425
    | exact resolve eq425 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq449 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq446
       have i₂ := eq111 x
       grind)
    | exact superpose eq111 eq446
    | exact resolve eq446 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq446
  have eq467 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq268 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq268
    | (have j0 := eq268 X0 y
       grind)
    | exact resolve eq268 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq509 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X2 (M.op X1 X1)
       have i₂ := eq51 (M.op X1 X1) X0 X1
       grind)
    | (have i₁ := eq14 X3 X2 (M.op X1 X1)
       have i₂ := eq51 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq543 : (k (M.op y y) y) = (τ (k (M.op (σ y) (σ y)) (σ y))) := by
    first
    | exact superpose eq125 eq467
    | exact resolve eq467 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq467
  have eq604 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X4 (M.op X4 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq50 X1 X4 x x
       have i₂ := eq50 X1 X0 x x
       grind)
    | (have i₁ := eq50 X0 X1 x x
       have i₂ := eq50 X0 (M.op x x) x x
       grind)
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq609 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X2) (M.op X3 (M.op (M.op X4 X4) X0)))) = (M.op X3 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq50 (M.op X3 (M.op (M.op X4 X4) X0)) X3 X1 X2
       have i₂ := eq14 X0 X3 X4
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq623 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X2 X2) x
       have i₂ := eq50 X1 X0 X2 x
       grind)
    | (have i₁ := eq14 X0 (M.op X2 X2) X2
       have i₂ := eq50 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq659 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq277 X0
       grind)
    | exact superpose eq277 eq16
    | exact resolve eq16 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq818 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (τ (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 (τ X0)
       have i₂ := eq659 X0
       grind)
    | exact superpose eq659 eq14
    | exact resolve eq14 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq828 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op (M.op X1 X1) X0))) = (M.op (M.op X0 (M.op (M.op X1 X1) X0)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq838 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq604 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq604
    | (have j0 := eq604 x y X0
       grind)
    | exact resolve eq604 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq839 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq604
    | (have j0 := eq604 X0 (σ y) (σ x)
       grind)
    | exact resolve eq604 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq899 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y (M.op X0 X0) X0
       have i₂ := eq838 (M.op X0 X0)
       grind)
    | exact superpose eq838 eq14
    | exact resolve eq14 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq923 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq839 eq14
    | exact resolve eq14 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1044 : ∀ X0 : G, y = (M.op (τ (M.op X0 X0)) (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq899 (τ X0)
       have i₂ := eq659 X0
       grind)
    | exact superpose eq659 eq899
    | exact resolve eq899 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1062 : ∀ X0 : G, (σ y) = (M.op (τ (M.op X0 X0)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq923 (τ X0)
       have i₂ := eq659 X0
       grind)
    | exact superpose eq659 eq923
    | exact resolve eq923 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1150 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 X0)) (M.op X1 (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq623 X1 X2 (τ X0)
       have i₂ := eq659 X0
       grind)
    | exact superpose eq659 eq623
    | exact resolve eq623 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq1151 : ∀ X0 X1 X2 X3 : G, (M.op X3 X1) = (M.op (M.op X2 X2) (M.op X3 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq623 X3 (M.op X3 X1) X2
       have i₂ := eq604 X3 X1 X0
       grind)
    | (have i₁ := eq623 X3 (M.op X3 X1) X2
       have i₂ := eq604 X0 X1 X3
       grind)
    | exact superpose eq604 eq623
    | exact resolve eq623 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq7796 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X1) (M.op X2 (M.op X2 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq623 X2 X3 (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)))
       have i₂ := eq609 X1 (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1) X0
       grind)
    | exact superpose eq609 eq623
    | exact resolve eq623 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609 eq623
  have eq15134 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq89 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq15135 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq15134
    | exact resolve eq15134 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15134
  have eq15146 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15135
       have r₂ := eq27
       grind)
    | exact resolve eq15135 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15135
  have eq15150 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq15146
    | exact resolve eq15146 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15146
  have eq15152 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq15150
    | exact resolve eq15150 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15150
  have eq15237 : ∀ X0 : G, (σ x) = (M.op (τ (M.op X0 X0)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15152 eq1150
    | exact resolve eq1150 eq15152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15152
  have eq15242 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1062 eq15237
    | exact resolve eq15237 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062 eq15237
  have eq15329 : ∀ X0 : G, x = (M.op (τ (M.op X0 X0)) (M.op x (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1150 X0 x x
       have i₂ := eq15242
       grind)
    | exact superpose eq15242 eq1150
    | exact resolve eq1150 eq15242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150 eq15242
  have eq15334 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1044 eq15329
    | exact resolve eq15329 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044 eq15329
  have eq16067 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (σ x))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15334 eq923
    | exact resolve eq923 eq15334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923 eq15334
  have eq23908 : ∀ X0 X2 : G, (M.op X0 (M.op X0 (M.op (σ y) X2))) = X2 ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0 X2
    first
    | exact superpose eq16067 eq509
    | exact resolve eq509 eq16067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23939 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op X0 (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16067 eq509
    | exact resolve eq509 eq16067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq24007 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (τ (σ y)) X1))) = X1 ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq16067 eq818
    | exact resolve eq818 eq16067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818 eq16067
  have eq24086 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op y X1))) = X1 ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq29 eq24007
    | exact resolve eq24007 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24007
  have eq24093 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq839 eq23939
    | (have j0 := eq23939 (σ x)
       grind)
    | exact resolve eq23939 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23939
  have eq32791 : (k (M.op (σ y) (σ y)) (σ y)) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23908 eq828
    | exact resolve eq828 eq23908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23908
  have eq32951 : (k (M.op (σ y) (σ y)) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq839 eq32791
    | exact resolve eq32791 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32791
  have eq35781 : (k (M.op y y) y) = (M.op y (M.op y y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq828 (M.op y y) y
       have i₂ := eq24086 (M.op y y) y
       grind)
    | exact superpose eq24086 eq828
    | exact resolve eq828 eq24086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828 eq24086
  have eq35958 : (M.op x (M.op x y)) = (k (M.op y y) y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35781
       have i₂ := eq838 y
       grind)
    | exact superpose eq838 eq35781
    | exact resolve eq35781 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838 eq35781
  have eq43233 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op X1 X1) (M.op X0 (M.op (σ x) (M.op (σ x) (σ x))))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq24093 eq1151
    | exact resolve eq1151 eq24093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24093
  have eq43744 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq43233 x x
       have i₂ := eq1151 sF2 sF2 x x
       grind)
    | exact superpose eq1151 eq43233
    | exact resolve eq43233 eq1151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151 eq43233
  have eq46113 : (k (M.op y y) y) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32951 eq543
    | exact resolve eq543 eq32951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543 eq32951
  have eq290694 : (M.op x (M.op x y)) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35958
       have i₂ := eq46113
       grind)
    | exact superpose eq46113 eq35958
    | exact resolve eq35958 eq46113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35958 eq46113
  have eq290700 : (M.op x (M.op x y)) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq290694
  have eq290731 : (M.op x (M.op x y)) = (τ (M.op (σ x) (σ x))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq43744 eq290700
    | exact resolve eq290700 eq43744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43744 eq290700
  have eq290945 : (M.op x (M.op x y)) = (τ (M.op (σ x) (σ x))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq290731
  have eq290948 : (M.op x x) = (M.op x (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq117 eq290945
    | exact resolve eq290945 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290945
  have eq291044 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op (M.op X0 X0) X1) X1) (M.op x (M.op x x))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq290948 eq7796
    | exact resolve eq7796 eq290948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290948
  have eq291108 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq291044 x x
       have i₂ := eq7796 x x x x
       grind)
    | exact superpose eq7796 eq291044
    | exact resolve eq291044 eq7796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291044
  have eq291109 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq291108
  have eq291130 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq291109 eq29
    | exact resolve eq29 eq291109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq291109
  have eq291322 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq291130
    | exact resolve eq291130 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq291130
  have eq291323 : x = (M.op x y) ∨ x = y := by grind
  clear eq291322
  have eq291342 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq291323 eq20
    | exact resolve eq20 eq291323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq291408 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq291323 eq899
    | exact resolve eq899 eq291323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899 eq291323
  have eq291617 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq291342
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq291342
    | exact resolve eq291342 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291342
  have eq303848 : (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq449
       have i₂ := eq291408 x
       grind)
    | exact superpose eq291408 eq449
    | exact resolve eq449 eq291408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449 eq291408
  have eq304324 : (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq303848
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq303848
    | exact resolve eq303848 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303848
  have eq327974 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op X0 (σ y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq304324 eq14
    | exact resolve eq14 eq304324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304324
  have eq328484 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq839 eq327974
    | (have j0 := eq327974 (σ x)
       grind)
    | exact resolve eq327974 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839 eq327974
  have eq330795 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op X0 X0) X1) X1) (M.op (σ x) (M.op (σ x) (σ x)))) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq328484 eq7796
    | exact resolve eq7796 eq328484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328484
  have eq330848 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq330795 x x
       have i₂ := eq7796 x x sF2 sF2
       grind)
    | exact superpose eq7796 eq330795
    | exact resolve eq330795 eq7796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7796 eq330795
  have eq333588 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq330848 eq27
    | exact resolve eq27 eq330848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330848
  have eq333739 : x = y := by
    first
    | (have r₁ := eq333588
       have r₂ := eq291617
       grind)
    | exact resolve eq333588 eq291617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291617 eq333588
  have eq333740 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq333739
       grind)
    | exact superpose eq333739 eq18
    | exact resolve eq18 eq333739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq333741 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq333739
       grind)
    | exact superpose eq333739 eq24
    | exact resolve eq24 eq333739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq333739
  have eq334116 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq333741
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq333741
    | exact resolve eq333741 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq333741
  have eq334147 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq334116 eq26
    | exact resolve eq26 eq334116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq334116
  have eq334793 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq334147 eq117
    | exact resolve eq117 eq334147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq334147
  have eq335184 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq334793
       have i₂ := eq333740
       grind)
    | exact superpose eq333740 eq334793
    | exact resolve eq334793 eq333740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333740 eq334793
  have eq335201 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq335184 eq15
    | exact resolve eq15 eq335184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335184
  have eq335521 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq335201
    | exact resolve eq335201 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq335201
  have eq335621 : False := by grind
  exact eq335621

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,Y) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pyy_pyx_pxy_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq31 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq9 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X1) X0) (M.op X2 X2) X2
       have i₂ := eq9 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq85 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq10
    | exact resolve eq10 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq124 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq85
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq209 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X3 (M.op X1 X1) X2
       have i₂ := eq53 (M.op X1 X1) X0 X1
       grind)
    | (have i₁ := eq53 X3 (M.op X1 X1) X2
       have i₂ := eq53 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq124 X0 X0
       have i₂ := eq290 X0
       grind)
    | exact superpose eq290 eq124
    | exact resolve eq124 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq307 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq290 (σ X0)
       grind)
    | exact superpose eq290 eq15
    | exact resolve eq15 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq308 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq307 X0
       have i₂ := eq290 X0
       grind)
    | exact superpose eq290 eq307
    | exact resolve eq307 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq309 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq306 X0
       have i₂ := eq290 (τ X0)
       grind)
    | exact superpose eq290 eq306
    | exact resolve eq306 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290 eq306
  have eq1019 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq61
       have i₂ := eq14 sF2 sF3
       grind)
    | exact superpose eq14 eq61
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq1020 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq1019
    | exact resolve eq1019 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019
  have eq1024 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq1020
    | exact resolve eq1020 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1037 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X4 (M.op X4 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq52 X1 X4 x x
       have i₂ := eq52 X1 X0 x x
       grind)
    | (have i₁ := eq52 X0 X1 x x
       have i₂ := eq52 X0 (M.op x x) x x
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1055 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X2 X2) x
       have i₂ := eq52 X1 X0 X2 x
       grind)
    | (have i₁ := eq9 X0 (M.op X2 X2) X2
       have i₂ := eq52 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1060 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op X0 (M.op X0 (M.op X1 X1))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X3 (M.op (M.op X1 X1) (M.op X1 X1)) X2
       have i₂ := eq52 (M.op X1 X1) X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1104 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1037 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1037
    | (have j0 := eq1037 X0 y x
       grind)
    | exact resolve eq1037 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1105 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq1037
    | (have j0 := eq1037 X0 (σ y) (σ x)
       grind)
    | exact resolve eq1037 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1148 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq9 y (M.op X0 X0) X0
       have i₂ := eq1104 (M.op X0 X0)
       grind)
    | exact superpose eq1104 eq9
    | exact resolve eq9 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1153 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 y))) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1037 X0 (M.op X0 y) X1
       have i₂ := eq1104 X0
       grind)
    | (have i₁ := eq1037 x (M.op x y) x
       have i₂ := eq1104 X0
       grind)
    | exact superpose eq1104 eq1037
    | exact resolve eq1037 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1176 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1105 eq9
    | exact resolve eq9 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105
  have eq1233 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X3) X0)) = (M.op (M.op X1 X1) (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1055 X2 (M.op X2 (M.op (M.op X3 X3) X0)) X1
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq1055
    | exact resolve eq1055 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1234 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X0 X0) (M.op X1 (M.op x (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1055 X1 (M.op X1 y) X0
       have i₂ := eq1104 X1
       grind)
    | (have i₁ := eq1055 x (M.op x y) x
       have i₂ := eq1104 X0
       grind)
    | exact superpose eq1104 eq1055
    | exact resolve eq1055 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq1836 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (M.op (M.op x (M.op x y)) y) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1234 eq9
    | exact resolve eq9 eq1234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1841 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op x (M.op x y)) y) X1) := by
    intro X0 X1
    first
    | exact superpose eq1234 eq53
    | exact resolve eq53 eq1234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1845 : ∀ X0 X1 : G, (M.op (M.op (M.op x (M.op x y)) y) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1234 eq1055
    | exact resolve eq1055 eq1234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234
  have eq3308 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 X0)) = (M.op X2 (M.op (M.op (M.op x (M.op x y)) y) X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1836 eq1055
    | exact resolve eq1055 eq1836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3916 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (M.op x (M.op x y)) y) X0)) = (M.op (M.op (M.op x (M.op x y)) y) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq1836 eq1845
    | exact resolve eq1845 eq1836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836 eq1845
  have eq8384 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op y (M.op x (M.op x y))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq209 y (M.op y y) X0 X1
       have i₂ := eq1153 y (M.op y y)
       grind)
    | exact superpose eq1153 eq209
    | exact resolve eq209 eq1153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq1153
  have eq9427 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op (M.op y (M.op x (M.op x y))) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq8384 x X0
       grind)
    | exact superpose eq8384 eq9
    | exact resolve eq9 eq8384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9432 : ∀ X0 : G, (M.op (M.op (M.op x (M.op x y)) y) X0) = (M.op (M.op y (M.op x (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq1841 x X0
       have i₂ := eq8384 x X0
       grind)
    | exact superpose eq8384 eq1841
    | exact resolve eq1841 eq8384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1841 eq8384
  have eq10090 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 X0)) = (M.op X2 (M.op (M.op y (M.op x (M.op x y))) X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq9432 eq3308
    | exact resolve eq3308 eq9432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3308
  have eq10112 : ∀ X0 X1 : G, (M.op (M.op (M.op x (M.op x y)) y) (M.op X1 X0)) = (M.op X1 (M.op (M.op y (M.op x (M.op x y))) X0)) := by
    intro X0 X1
    first
    | exact superpose eq9432 eq3916
    | exact resolve eq3916 eq9432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3916
  have eq10571 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op y (M.op x (M.op x y))) X0)) = (M.op (M.op y (M.op x (M.op x y))) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq9432 eq10112
    | exact resolve eq10112 eq9432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9432 eq10112
  have eq15836 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op X1 (M.op X0 (M.op X0 X1))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1060 X1 X1 X2 X3
       have i₂ := eq1037 X1 X1 X0
       grind)
    | (have i₁ := eq1060 X1 X1 X2 X3
       have i₂ := eq1037 X0 X1 X1
       grind)
    | exact superpose eq1037 eq1060
    | exact resolve eq1060 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037 eq1060
  have eq25588 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X0 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1055 X0 X2 x
       have i₂ := eq1233 (M.op X0 X2) x X0 X1
       grind)
    | (have i₁ := eq1055 (M.op x x) X1 X2
       have i₂ := eq1233 (M.op (M.op x x) X1) X1 (M.op X2 X2) x
       grind)
    | exact superpose eq1233 eq1055
    | exact resolve eq1055 eq1233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055 eq1233
  have eq30694 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 (M.op X1 (M.op X1 X0))) (M.op X2 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25588 X2 x X3
       have i₂ := eq15836 X1 X0 x (M.op X2 X3)
       grind)
    | exact superpose eq15836 eq25588
    | exact resolve eq25588 eq15836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15836 eq25588
  have eq87623 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq1024
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq1024
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq1024 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq87665 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq87623
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq87623
    | exact resolve eq87623 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87623
  have eq87668 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op y y) = (M.op y x) := by
    first
    | exact superpose eq20 eq87665
    | exact resolve eq87665 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87665
  have eq87669 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have r₁ := eq87668
       have r₂ := eq27
       grind)
    | exact resolve eq87668 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87668
  have eq87670 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq87669
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq87669
    | exact resolve eq87669 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87669
  have eq87834 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (M.op X0 (M.op X1 (M.op X1 X0))) (M.op (σ y) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op y y) = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq87670 eq30694
    | exact resolve eq30694 eq87670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87670
  have eq87836 : (M.op y y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq87834 x x
       have i₂ := eq30694 x x sF3 sF2
       grind)
    | exact superpose eq30694 eq87834
    | exact resolve eq87834 eq30694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87834
  have eq88023 : ∀ X0 X1 : G, y = (M.op y (M.op (M.op X0 (M.op X1 (M.op X1 X0))) (M.op y x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq30694 X0 X1 y y
       have i₂ := eq87836
       grind)
    | exact superpose eq87836 eq30694
    | exact resolve eq30694 eq87836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87836
  have eq88025 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq88023 x x
       have i₂ := eq30694 x x y x
       grind)
    | exact superpose eq30694 eq88023
    | exact resolve eq88023 eq30694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30694 eq88023
  have eq88049 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (σ x))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq88025 eq1176
    | exact resolve eq1176 eq88025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176 eq88025
  have eq94433 : (τ (σ y)) = (M.op (τ (M.op (σ x) (σ x))) (τ (M.op (σ x) (σ x)))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq88049 eq309
    | exact resolve eq309 eq88049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88049
  have eq94617 : (τ (σ y)) = (M.op (M.op (τ (σ x)) (τ (σ x))) (M.op (τ (σ x)) (τ (σ x)))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq94433
       have i₂ := eq309 sF2
       grind)
    | exact superpose eq309 eq94433
    | exact resolve eq94433 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309 eq94433
  have eq94688 : (τ (σ y)) = (M.op (τ (σ x)) (M.op (M.op y (M.op x (M.op x y))) (τ (σ x)))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq94617
       have i₂ := eq10090 (τ sF2) (τ sF2) (τ sF2)
       grind)
    | exact superpose eq10090 eq94617
    | exact resolve eq94617 eq10090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94617
  have eq94732 : (τ (σ y)) = (M.op (M.op y (M.op x (M.op x y))) (M.op (τ (σ x)) (τ (σ x)))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq10571 eq94688
    | exact resolve eq94688 eq10571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94688
  have eq94740 : (τ (σ y)) = (M.op (M.op y (M.op x (M.op x y))) (M.op x x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq38 eq94732
    | exact resolve eq94732 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94732
  have eq94742 : (τ (σ y)) = (M.op x (M.op (M.op y (M.op x (M.op x y))) x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq10571 eq94740
    | exact resolve eq94740 eq10571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94740
  have eq94744 : y = (M.op x (M.op (M.op y (M.op x (M.op x y))) x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq39 eq94742
    | exact resolve eq94742 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94742
  have eq191382 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq94744 eq9427
    | exact resolve eq9427 eq94744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94744
  have eq191410 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq191382
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq191382
    | exact resolve eq191382 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191382
  have eq191411 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq191410
  have eq191426 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq191411 eq39
    | exact resolve eq39 eq191411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq191411
  have eq191553 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq191426
    | exact resolve eq191426 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq191426
  have eq191554 : x = (M.op x y) ∨ x = y := by grind
  clear eq191553
  have eq191563 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq191554 eq20
    | exact resolve eq20 eq191554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191590 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq191554 eq1148
    | exact resolve eq1148 eq191554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148 eq191554
  have eq191657 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq191563
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq191563
    | exact resolve eq191563 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191563
  have eq195141 : (σ y) = (M.op (σ (M.op x x)) (σ (M.op x x))) ∨ x = y := by
    first
    | (have i₁ := eq308 (M.op x x)
       have i₂ := eq191590 x
       grind)
    | exact superpose eq191590 eq308
    | exact resolve eq308 eq191590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191590
  have eq195422 : (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq195141
       have i₂ := eq308 x
       grind)
    | exact superpose eq308 eq195141
    | exact resolve eq195141 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195141
  have eq195472 : (σ y) = (M.op (σ x) (M.op (M.op y (M.op x (M.op x y))) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq195422
       have i₂ := eq10090 (σ x) (σ x) (σ x)
       grind)
    | exact superpose eq10090 eq195422
    | exact resolve eq195422 eq10090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10090 eq195422
  have eq195511 : (σ y) = (M.op (M.op y (M.op x (M.op x y))) (M.op (σ x) (σ x))) ∨ x = y := by
    first
    | exact superpose eq10571 eq195472
    | exact resolve eq195472 eq10571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195472
  have eq195516 : (σ y) = (M.op (M.op y (M.op x (M.op x y))) (M.op (σ x) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq195511
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq195511
    | exact resolve eq195511 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195511
  have eq195518 : (σ y) = (M.op (σ x) (M.op (M.op y (M.op x (M.op x y))) (σ x))) ∨ x = y := by
    first
    | exact superpose eq10571 eq195516
    | exact resolve eq195516 eq10571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10571 eq195516
  have eq195520 : (σ y) = (M.op (σ x) (M.op (M.op y (M.op x (M.op x y))) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq195518
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq195518
    | exact resolve eq195518 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195518
  have eq243013 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq195520 eq9427
    | exact resolve eq9427 eq195520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9427 eq195520
  have eq243102 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq243013
    | exact resolve eq243013 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243013
  have eq243111 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq243102 eq27
    | exact resolve eq27 eq243102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243102
  have eq243285 : x = y := by
    first
    | (have r₁ := eq243111
       have r₂ := eq191657
       grind)
    | exact resolve eq243111 eq191657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191657 eq243111
  have eq243288 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq243285
       grind)
    | exact superpose eq243285 eq18
    | exact resolve eq18 eq243285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq243289 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq243285
       grind)
    | exact superpose eq243285 eq24
    | exact resolve eq24 eq243285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq243285
  have eq258562 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq243289
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq243289
    | exact resolve eq243289 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243289
  have eq259609 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq258562 eq26
    | exact resolve eq26 eq258562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq258562
  have eq264104 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq308 x
       have i₂ := eq243288
       grind)
    | exact superpose eq243288 eq308
    | exact resolve eq308 eq243288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308 eq243288
  have eq266356 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq264104
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq264104
    | exact resolve eq264104 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq264104
  have eq268734 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq259609 eq266356
    | exact resolve eq266356 eq259609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259609 eq266356
  have eq270477 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq268734
    | exact resolve eq268734 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq268734
  have eq271529 : False := by grind
  exact eq271529

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pxy_pxx_pxy_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq18
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
  clear eq19
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq9 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X1) X0) (M.op X2 X2) X2
       have i₂ := eq9 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X2 X3 (M.op X1 X1)
       have i₂ := eq53 (M.op X1 X1) X0 X1
       grind)
    | (have i₁ := eq53 X2 X3 (M.op X1 X1)
       have i₂ := eq53 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X2 (M.op X1 X1)
       have i₂ := eq53 (M.op X1 X1) X0 X1
       grind)
    | (have i₁ := eq9 X3 X2 (M.op X1 X1)
       have i₂ := eq53 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k (M.op X1 (M.op (M.op X2 X2) X0)) X1) = (M.op (M.op X1 (M.op (M.op X2 X2) X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 (M.op (M.op X2 X2) X0)) X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X1 (M.op (M.op X2 X2) X0)) X1
       grind)
    | (have r₁ := eq12 (M.op X0 (M.op (M.op X2 X2) X0)) X0
       have r₂ := eq9 X0 X0 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op X4 X3)) = (M.op (M.op X0 (M.op X0 (M.op X1 X1))) (M.op (M.op X2 X2) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X3 X4 (M.op (M.op X1 X1) (M.op X1 X1)) X2
       have i₂ := eq52 (M.op X1 X1) X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X4 (M.op X4 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq52 X1 X4 x x
       have i₂ := eq52 X1 X0 x x
       grind)
    | (have i₁ := eq52 X0 X1 x x
       have i₂ := eq52 X0 (M.op x x) x x
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X4 X4) X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq9 (M.op (M.op X4 X4) X1) X2 x
       have i₂ := eq52 X1 X0 x X4
       grind)
    | (have i₁ := eq9 (M.op (M.op X2 X2) X0) X1 X2
       have i₂ := eq52 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X2 X2) x
       have i₂ := eq52 X1 X0 X2 x
       grind)
    | (have i₁ := eq9 X0 (M.op X2 X2) X2
       have i₂ := eq52 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op X0 (M.op X0 (M.op X1 X1))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X3 (M.op (M.op X1 X1) (M.op X1 X1)) X2
       have i₂ := eq52 (M.op X1 X1) X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op (M.op X0 (M.op X0 (M.op X1 X1))) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X2 (M.op (M.op X1 X1) (M.op X1 X1))
       have i₂ := eq52 (M.op X1 X1) X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X0 X1))) = (M.op X3 (M.op X3 (M.op X2 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq96 X2 (M.op X2 X1) X3
       have i₂ := eq96 X2 X1 X0
       grind)
    | (have i₁ := eq96 X2 (M.op X2 X1) X3
       have i₂ := eq96 X0 X1 X2
       grind)
    | exact superpose eq96 eq96
    | exact resolve eq96 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) (M.op X4 X1))) = (M.op X4 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X4 X1) X4 X2 X3
       have i₂ := eq96 X4 X1 X0
       grind)
    | (have i₁ := eq52 (M.op X4 X1) X4 X2 X3
       have i₂ := eq96 X0 X1 X4
       grind)
    | exact superpose eq96 eq52
    | exact resolve eq52 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq182 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq14 (M.op (M.op X1 X1) X0) X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 (M.op X2 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq114 X2 X3 (M.op X1 X1)
       have i₂ := eq53 (M.op X1 X1) X0 X1
       grind)
    | (have i₁ := eq114 X2 X3 (M.op X1 X1)
       have i₂ := eq53 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq53 eq114
    | exact resolve eq114 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X3) X0)) = (M.op (M.op X1 X1) (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq114 X2 (M.op X2 (M.op (M.op X3 X3) X0)) X1
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq114
    | exact resolve eq114 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 X2 X3 : G, (M.op X3 X1) = (M.op (M.op X2 X2) (M.op X3 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq114 X3 (M.op X3 X1) X2
       have i₂ := eq96 X3 X1 X0
       grind)
    | (have i₁ := eq114 X3 (M.op X3 X1) X2
       have i₂ := eq96 X0 X1 X3
       grind)
    | exact superpose eq96 eq114
    | exact resolve eq114 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq182 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq182
    | (have j0 := eq182 (σ X0) (σ X1)
       grind)
    | exact resolve eq182 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq182 (σ X0) X1
       grind)
    | exact superpose eq182 eq29
    | (have j1 := eq182 (σ X0) X1
       grind)
    | exact resolve eq29 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq560 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq223 x y
       grind)
    | exact superpose eq223 eq16
    | (have j1 := eq223 x y
       grind)
    | exact resolve eq16 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq656 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op (M.op (M.op X3 X3) (M.op X4 X4)) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq96 X1 (M.op X2 (M.op (M.op (M.op X3 X3) (M.op X4 X4)) X0)) X2
       have i₂ := eq75 X3 X4 X2 X0
       grind)
    | exact superpose eq75 eq96
    | exact resolve eq96 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq690 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X3 (M.op X4 (M.op X4 (M.op X2 (M.op X2 X0)))))) = X0 := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq113 X4 (M.op X2 (M.op X2 X0)) X3 x
       have i₂ := eq114 X2 X0 x
       grind)
    | exact superpose eq114 eq113
    | exact resolve eq113 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq808 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X4 (M.op X4 X1))) = (M.op (M.op X2 X2) (M.op X3 (M.op (M.op X0 X0) X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq114 X3 (M.op X3 (M.op X4 (M.op X4 X1))) X2
       have i₂ := eq113 X4 X1 X3 X0
       grind)
    | exact superpose eq113 eq114
    | exact resolve eq114 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq809 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X0 X0) X1)) = (M.op X2 (M.op X2 (M.op X3 (M.op X4 (M.op X4 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq96 X2 (M.op X3 (M.op X4 (M.op X4 X1))) X3
       have i₂ := eq113 X4 X1 X3 X0
       grind)
    | exact superpose eq113 eq96
    | exact resolve eq96 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq113
  have eq1172 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op X2 X0)) = (M.op X2 (M.op (M.op X3 (M.op X3 (M.op X4 X4))) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq114 X2 (M.op X2 (M.op (M.op X3 (M.op X3 (M.op X4 X4))) X0)) X1
       have i₂ := eq118 X3 X4 X2 X0
       grind)
    | exact superpose eq118 eq114
    | exact resolve eq114 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq1536 : ∀ X0 X1 : G, (k (M.op X0 (M.op (M.op X1 X1) X0)) X0) = (M.op (M.op X0 (M.op (M.op X1 X1) X0)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq1846 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X3) X4) = (M.op (M.op (M.op X5 X5) (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X1 X2)) X2)))) X4) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq64 X5 (M.op X1 (M.op X1 X2)) X4 X3
       have i₂ := eq131 X1 X2 (M.op X1 (M.op X1 X2)) X0
       grind)
    | exact superpose eq131 eq64
    | exact resolve eq64 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq1954 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X3) X4) = (M.op (M.op (M.op X1 (M.op X1 X2)) X2) X4) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq1846 x X1 X2 X3 X4 x
       have i₂ := eq114 x (M.op (M.op X1 (M.op X1 X2)) X2) x
       grind)
    | exact superpose eq114 eq1846
    | exact resolve eq1846 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1846
  have eq2201 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 X3) (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X1 X2)) X2)))) (M.op X4 (M.op X4 X5))) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq184 X3 (M.op X1 (M.op X1 X2)) X4 X5
       have i₂ := eq131 X1 X2 (M.op X1 (M.op X1 X2)) X0
       grind)
    | exact superpose eq131 eq184
    | exact resolve eq184 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2378 : ∀ X1 X2 X4 X5 : G, (M.op (M.op (M.op X1 (M.op X1 X2)) X2) (M.op X4 (M.op X4 X5))) = X5 := by
    intro X1 X2 X4 X5
    first
    | (have i₁ := eq2201 x X1 X2 x X4 X5
       have i₂ := eq114 x (M.op (M.op X1 (M.op X1 X2)) X2) x
       grind)
    | exact superpose eq114 eq2201
    | exact resolve eq2201 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2201
  have eq2563 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X2) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq186 (M.op X1 X0) x X1 X2
       have i₂ := eq114 X1 X0 x
       grind)
    | exact superpose eq114 eq186
    | exact resolve eq186 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq3391 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq560
       have i₂ := eq182 x y
       grind)
    | exact superpose eq182 eq560
    | (have j1 := eq182 (σ x) (σ y)
       grind)
    | exact resolve eq560 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq3394 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq3391
  have eq3426 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12 (σ y) (σ y)
       have i₂ := eq3394
       grind)
    | exact superpose eq3394 eq12
    | exact resolve eq12 eq3394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3438 : (σ x) = (σ (k y y)) ∨ (σ x) ≠ (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3426
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq3426
    | exact resolve eq3426 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3426
  have eq4556 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X0 (M.op X0 (M.op X1 X1))) (M.op (M.op X2 X2) (M.op X3 (M.op X4 (M.op X4 X5)))))) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq690 X5 X4 X3 X3
       have i₂ := eq85 X0 X1 X2 (M.op X3 (M.op X4 (M.op X4 X5))) X3
       grind)
    | exact superpose eq85 eq690
    | exact resolve eq690 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq690
  have eq4739 : ∀ X0 X1 X3 X5 : G, (M.op X3 (M.op (M.op X0 (M.op X0 (M.op X1 X1))) (M.op X3 X5))) = X5 := by
    intro X0 X1 X3 X5
    first
    | (have i₁ := eq4556 X0 X1 x X3 x X5
       have i₂ := eq187 x X5 x X3
       grind)
    | exact superpose eq187 eq4556
    | exact resolve eq4556 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4556
  have eq13882 : ∀ X0 X1 X2 X3 : G, (k (M.op (M.op X0 X0) (M.op (M.op X1 X1) (M.op X2 (M.op X2 (M.op X3 X3))))) (M.op X2 (M.op X2 (M.op X3 X3)))) = (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X1) (M.op X2 (M.op X2 (M.op X3 X3))))) (M.op X2 (M.op X2 (M.op X3 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1536 (M.op X0 (M.op X0 (M.op X1 X1))) X1
       have i₂ := eq116 X0 X1 X2 (M.op (M.op X1 X1) (M.op X0 (M.op X0 (M.op X1 X1))))
       grind)
    | exact superpose eq116 eq1536
    | exact resolve eq1536 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq1536
  have eq13903 : ∀ X1 X2 X3 : G, (k (M.op (M.op X1 X1) (M.op X3 X3)) (M.op X2 (M.op X2 (M.op X3 X3)))) = (M.op (M.op (M.op X1 X1) (M.op X3 X3)) (M.op X2 (M.op X2 (M.op X3 X3)))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq13882 X2 X1 x X3
       have i₂ := eq187 x (M.op X3 X3) X2 (M.op X1 X1)
       grind)
    | exact superpose eq187 eq13882
    | exact resolve eq13882 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq13882
  have eq13920 : ∀ X1 X2 X3 : G, (M.op X3 X3) = (k (M.op (M.op X1 X1) (M.op X3 X3)) (M.op X2 (M.op X2 (M.op X3 X3)))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq13903 X1 X2 X3
       have i₂ := eq184 X1 X3 X2 (M.op X3 X3)
       grind)
    | exact superpose eq184 eq13903
    | exact resolve eq13903 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq13903
  have eq63965 : (k y (τ (σ y))) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq226 y (σ y)
       have i₂ := eq3394
       grind)
    | exact superpose eq3394 eq226
    | exact resolve eq226 eq3394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq3394
  have eq64052 : x = (k y (τ (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq63965
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq63965
    | exact resolve eq63965 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63965
  have eq64058 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq64052
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq64052
    | exact resolve eq64052 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64052
  have eq64114 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq182 y y
       have i₂ := eq64058
       grind)
    | exact superpose eq64058 eq182
    | (have j0 := eq182 x y
       grind)
    | exact resolve eq182 eq64058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64115 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq64114
  have eq64272 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq64115
       grind)
    | exact superpose eq64115 eq12
    | (have r₁ := eq12 y y
       have r₂ := eq64115
       grind)
    | exact resolve eq12 eq64115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64315 : x ≠ y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq64115
  have eq64316 : y = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq64272
  have eq68678 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq64058
       have i₂ := eq64316
       grind)
    | exact superpose eq64316 eq64058
    | exact resolve eq64058 eq64316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64058 eq64316
  have eq68707 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq68678
  have eq68710 : x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq68707
       have r₂ := eq64315
       grind)
    | exact resolve eq68707 eq64315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64315 eq68707
  have eq165454 : (σ x) = (σ (k y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq3438
       have r₂ := eq68710
       grind)
    | exact resolve eq3438 eq68710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3438 eq68710
  have eq165467 : (k y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq165454
       grind)
    | exact superpose eq165454 eq10
    | exact resolve eq10 eq165454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165454
  have eq165491 : x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq165467
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq165467
    | exact resolve eq165467 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165467
  have eq165516 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq182 y y
       have i₂ := eq165491
       grind)
    | exact superpose eq165491 eq182
    | (have j0 := eq182 x y
       grind)
    | exact resolve eq182 eq165491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165517 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq165516
  have eq165784 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq165517
       grind)
    | exact superpose eq165517 eq12
    | (have r₁ := eq12 y y
       have r₂ := eq165517
       grind)
    | exact resolve eq12 eq165517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165845 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq165517
  have eq165846 : y = (k y y) ∨ x = (M.op y y) := by grind
  clear eq165784
  have eq165851 : x = y ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq165491
       have i₂ := eq165846
       grind)
    | exact superpose eq165846 eq165491
    | exact resolve eq165491 eq165846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165491 eq165846
  have eq165886 : x = y ∨ x = (M.op y y) := by grind
  clear eq165851
  have eq165890 : x = (M.op y y) := by
    first
    | (have r₁ := eq165886
       have r₂ := eq165845
       grind)
    | exact resolve eq165886 eq165845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165845 eq165886
  have eq165905 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op x X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 y
       have i₂ := eq165890
       grind)
    | exact superpose eq165890 eq9
    | exact resolve eq9 eq165890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165909 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1 y
       have i₂ := eq165890
       grind)
    | exact superpose eq165890 eq53
    | exact resolve eq53 eq165890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq165940 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq114 X0 X1 y
       have i₂ := eq165890
       grind)
    | exact superpose eq165890 eq114
    | exact resolve eq114 eq165890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq166100 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2563 X1 X0 y
       have i₂ := eq165890
       grind)
    | exact superpose eq165890 eq2563
    | exact resolve eq2563 eq165890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2563
  have eq171075 : y = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq166100 y y
       have i₂ := eq165890
       grind)
    | exact superpose eq165890 eq166100
    | exact resolve eq166100 eq165890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166100
  have eq172206 : y ≠ y ∨ (k (M.op x x) y) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq12 (M.op x x) y
       have i₂ := eq171075
       grind)
    | exact superpose eq171075 eq12
    | (have j0 := eq12 (M.op x x) y
       grind)
    | (have r₁ := eq12 (M.op x x) y
       have r₂ := eq171075
       grind)
    | exact resolve eq12 eq171075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171075
  have eq172269 : (k (M.op x x) y) = (M.op (M.op x x) y) := by grind
  clear eq172206
  have eq172311 : (M.op x y) = (k (M.op x x) y) := by
    first
    | (have i₁ := eq172269
       have i₂ := eq165909 y x
       grind)
    | exact superpose eq165909 eq172269
    | exact resolve eq172269 eq165909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172269
  have eq177019 : ∀ X0 X1 X3 X4 : G, (M.op X3 (M.op X4 (M.op X4 X1))) = (M.op x (M.op X3 (M.op (M.op X0 X0) X1))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq808 X0 X1 x X3 X4
       have i₂ := eq165909 (M.op X3 (M.op (M.op X0 X0) X1)) x
       grind)
    | exact superpose eq165909 eq808
    | exact resolve eq808 eq165909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq177020 : ∀ X1 X3 X4 : G, (M.op X3 (M.op X4 (M.op X4 X1))) = (M.op x (M.op X3 (M.op x X1))) := by
    intro X1 X3 X4
    first
    | (have i₁ := eq177019 x X1 X3 X4
       have i₂ := eq165909 X1 x
       grind)
    | exact superpose eq165909 eq177019
    | exact resolve eq177019 eq165909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177019
  have eq177716 : ∀ X0 X1 X2 X3 X4 : G, (M.op x (M.op X1 X0)) = (M.op X1 (M.op X2 (M.op X2 (M.op x (M.op (M.op (M.op X3 X3) (M.op X4 X4)) X0))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq177020 (M.op x (M.op (M.op (M.op X3 X3) (M.op X4 X4)) X0)) X1 X2
       have i₂ := eq75 X3 X4 x X0
       grind)
    | exact superpose eq75 eq177020
    | exact resolve eq177020 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq178780 : ∀ X0 X1 X2 X3 : G, (M.op x X1) = (M.op (M.op (M.op X2 (M.op X2 X3)) X3) (M.op x (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2378 X2 X3 x (M.op x X1)
       have i₂ := eq177020 X1 x X0
       grind)
    | (have i₁ := eq2378 X1 X2 x (M.op x X1)
       have i₂ := eq177020 X1 x x
       grind)
    | exact superpose eq177020 eq2378
    | exact resolve eq2378 eq177020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2378
  have eq178819 : ∀ X0 X1 X2 X3 : G, (M.op x (M.op X0 (M.op X1 (M.op X1 X2)))) = (M.op X0 (M.op X3 (M.op X3 (M.op x X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq131 X3 (M.op x X2) X0 x
       have i₂ := eq177020 X2 X0 X1
       grind)
    | (have i₁ := eq131 X0 (M.op x X1) x X3
       have i₂ := eq177020 X1 X3 x
       grind)
    | exact superpose eq177020 eq131
    | exact resolve eq131 eq177020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq177020
  have eq178935 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op x (M.op X0 (M.op X1 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq178819 X0 X1 X2 x
       have i₂ := eq165905 x X2
       grind)
    | exact superpose eq165905 eq178819
    | exact resolve eq178819 eq165905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165905 eq178819
  have eq178947 : ∀ X1 X2 X3 : G, (M.op (M.op (M.op X2 (M.op X2 X3)) X3) X1) = (M.op x X1) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq178780 x X1 X2 X3
       have i₂ := eq165940 x X1
       grind)
    | exact superpose eq165940 eq178780
    | exact resolve eq178780 eq165940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178780
  have eq179749 : ∀ X0 X1 : G, (M.op x (M.op X1 X0)) = (M.op X1 (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq177716 X0 X1 x x x
       have i₂ := eq656 X0 x x x x
       grind)
    | exact superpose eq656 eq177716
    | exact resolve eq177716 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656 eq177716
  have eq181070 : ∀ X1 X2 X3 X4 : G, (M.op X2 (M.op X2 (M.op X3 (M.op X4 (M.op X4 X1))))) = (M.op X3 (M.op x X1)) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq809 x X1 X2 X3 X4
       have i₂ := eq165909 X1 x
       grind)
    | exact superpose eq165909 eq809
    | exact resolve eq809 eq165909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq197915 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) ≠ X0 ∨ (k (M.op x X1) X0) = (M.op (M.op x X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op x X1) X0
       have i₂ := eq179749 X1 X0
       grind)
    | (have i₁ := eq12 (M.op X1 X0) x
       have i₂ := eq179749 X0 X1
       grind)
    | exact superpose eq179749 eq12
    | (have j0 := eq12 (M.op x X1) X0
       grind)
    | exact resolve eq12 eq179749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179749
  have eq224147 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 (M.op X3 (M.op X4 X4))) X0)) = (M.op x (M.op X2 X0)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq1172 X0 x X2 X3 X4
       have i₂ := eq165909 (M.op X2 X0) x
       grind)
    | exact superpose eq165909 eq1172
    | exact resolve eq1172 eq165909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq280925 : ∀ X2 X3 : G, (M.op X3 X3) = (k (M.op x (M.op X3 X3)) (M.op X2 (M.op X2 (M.op X3 X3)))) := by
    intro X2 X3
    first
    | (have i₁ := eq13920 x X2 X3
       have i₂ := eq165909 (M.op X3 X3) x
       grind)
    | exact superpose eq165909 eq13920
    | exact resolve eq13920 eq165909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13920
  have eq280981 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (k (M.op x (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X2 (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq280925 X2 (M.op (M.op X1 X1) (M.op X1 X1))
       have i₂ := eq161 X0 X1 (M.op X1 X1) X1 X1
       grind)
    | (have i₁ := eq280925 X2 (M.op X0 (M.op X0 X1))
       have i₂ := eq161 X0 X1 X2 x (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq161 eq280925
    | exact resolve eq280925 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161 eq280925
  have eq281925 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (k (M.op x (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X0 (M.op x X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq280981 X0 X1 x
       have i₂ := eq181070 X0 x X0 X1
       grind)
    | exact superpose eq181070 eq280981
    | exact resolve eq280981 eq181070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181070 eq280981
  have eq282300 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (k (M.op X0 X0) (M.op X0 (M.op x X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq281925 X0 X1
       have i₂ := eq178935 X0 X1 X0
       grind)
    | exact superpose eq178935 eq281925
    | exact resolve eq281925 eq178935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281925
  have eq543425 : ∀ X0 : G, (M.op X0 X0) = (M.op x (k (M.op X0 X0) (M.op X0 (M.op x X0)))) := by
    intro X0
    first
    | (have i₁ := eq178935 X0 x X0
       have i₂ := eq282300 X0 x
       grind)
    | exact superpose eq282300 eq178935
    | exact resolve eq178935 eq282300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178935
  have eq1012278 : ∀ X0 X1 : G, (M.op x (k (M.op X0 X0) (M.op X0 (M.op x X0)))) ≠ X0 ∨ (M.op (M.op x (M.op X1 (M.op X1 X0))) X0) = (k (M.op x (M.op X1 (M.op X1 X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq197915 X0 (M.op X1 (M.op X1 X0))
       have i₂ := eq282300 X0 X1
       grind)
    | exact superpose eq282300 eq197915
    | (have j0 := eq197915 X0 (M.op X1 (M.op X1 X0))
       grind)
    | (have r₁ := eq197915 (k (M.op x x) (M.op x (M.op x x))) (M.op (k (M.op x x) (M.op x (M.op x x))) x)
       have r₂ := eq282300 x (k (M.op x x) (M.op x (M.op x x)))
       grind)
    | exact resolve eq197915 eq282300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282300
  have eq1013261 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op (M.op x (M.op X1 (M.op X1 X0))) X0) = (k (M.op x (M.op X1 (M.op X1 X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1012278 X0 X1
       have i₂ := eq543425 X0
       grind)
    | exact superpose eq543425 eq1012278
    | (have j0 := eq1012278 X0 X1
       grind)
    | exact resolve eq1012278 eq543425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543425 eq1012278
  have eq1013513 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq1013261 x X0
       have i₂ := eq165940 X0 x
       grind)
    | exact superpose eq165940 eq1013261
    | (have j0 := eq1013261 X0 x
       grind)
    | exact resolve eq1013261 eq165940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165940 eq1013261
  have eq1013625 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1013513 X0
       have j1 := eq182 X0 X0
       grind)
    | (have r₁ := eq1013513 X0
       have r₂ := eq182 X0 X0
       grind)
    | (have r₁ := eq1013513 (M.op x x)
       have r₂ := eq182 (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact resolve eq1013513 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq1013513
  have eq1013844 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1013625 (σ X0)
       grind)
    | exact superpose eq1013625 eq15
    | exact resolve eq15 eq1013625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1013917 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1013844 X0
       have i₂ := eq1013625 X0
       grind)
    | exact superpose eq1013625 eq1013844
    | exact resolve eq1013844 eq1013625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013625 eq1013844
  have eq1015725 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 (M.op X2 X3)) X3) X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1954 X2 X3 (σ X0) X1
       have i₂ := eq1013917 X0
       grind)
    | exact superpose eq1013917 eq1954
    | exact resolve eq1954 eq1013917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1954
  have eq1015935 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op (M.op X1 (M.op X1 (M.op X2 X2))) (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4739 X1 X2 (σ X0) (σ X0)
       have i₂ := eq1013917 X0
       grind)
    | exact superpose eq1013917 eq4739
    | exact resolve eq4739 eq1013917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4739
  have eq1016022 : ∀ X0 : G, (σ X0) = (M.op x (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1015935 X0 x x
       have i₂ := eq224147 (σ (M.op X0 X0)) (σ X0) x x
       grind)
    | exact superpose eq224147 eq1015935
    | exact resolve eq1015935 eq224147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224147 eq1015935
  have eq1016173 : ∀ X0 X1 : G, (M.op x X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1015725 X0 X1 x x
       have i₂ := eq178947 X1 x x
       grind)
    | exact superpose eq178947 eq1015725
    | exact resolve eq1015725 eq178947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178947 eq1015725
  have eq1025589 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq1016173 y X0
       have i₂ := eq165890
       grind)
    | exact superpose eq165890 eq1016173
    | exact resolve eq1016173 eq165890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016173
  have eq1029889 : (M.op x (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1025589 (σ x)
       have i₂ := eq1013917 x
       grind)
    | exact superpose eq1013917 eq1025589
    | exact resolve eq1025589 eq1013917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013917
  have eq1030096 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1025589 (σ y)
       grind)
    | exact superpose eq1025589 eq16
    | exact resolve eq16 eq1025589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1030403 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq165909 X0 (σ x)
       have i₂ := eq1025589 (σ x)
       grind)
    | exact superpose eq1025589 eq165909
    | exact resolve eq165909 eq1025589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165909 eq1025589
  have eq1033569 : (M.op x x) = (τ (M.op x (σ x))) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1029889
       grind)
    | exact superpose eq1029889 eq10
    | exact resolve eq10 eq1029889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029889
  have eq1087618 : (σ y) = (M.op x (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq1016022 y
       have i₂ := eq165890
       grind)
    | exact superpose eq165890 eq1016022
    | exact resolve eq1016022 eq165890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165890 eq1016022
  have eq1088497 : (σ y) ≠ (σ y) ∨ (k (M.op x (σ x)) (σ y)) = (M.op (M.op x (σ x)) (σ y)) := by
    first
    | (have i₁ := eq197915 (σ y) (σ x)
       have i₂ := eq1087618
       grind)
    | exact superpose eq1087618 eq197915
    | (have j0 := eq197915 (σ y) (σ x)
       grind)
    | (have r₁ := eq197915 (σ y) (σ x)
       have r₂ := eq1087618
       grind)
    | exact resolve eq197915 eq1087618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197915 eq1087618
  have eq1088652 : (k (M.op x (σ x)) (σ y)) = (M.op (M.op x (σ x)) (σ y)) := by grind
  clear eq1088497
  have eq1088726 : (M.op x (σ y)) = (k (M.op x (σ x)) (σ y)) := by
    first
    | (have i₁ := eq1088652
       have i₂ := eq1030403 (σ y)
       grind)
    | exact superpose eq1030403 eq1088652
    | exact resolve eq1088652 eq1030403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030403 eq1088652
  have eq1161854 : (τ (M.op x (σ y))) = (k (τ (M.op x (σ x))) y) := by
    first
    | (have i₁ := eq23 (M.op x (σ x)) y
       have i₂ := eq1088726
       grind)
    | exact superpose eq1088726 eq23
    | exact resolve eq23 eq1088726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1088726
  have eq1161906 : (k (M.op x x) y) = (τ (M.op x (σ y))) := by
    first
    | (have i₁ := eq1161854
       have i₂ := eq1033569
       grind)
    | exact superpose eq1033569 eq1161854
    | exact resolve eq1161854 eq1033569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033569 eq1161854
  have eq1161925 : (M.op x y) = (τ (M.op x (σ y))) := by
    first
    | (have i₁ := eq1161906
       have i₂ := eq172311
       grind)
    | exact superpose eq172311 eq1161906
    | exact resolve eq1161906 eq172311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172311 eq1161906
  have eq1161956 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq11 (M.op x (σ y))
       have i₂ := eq1161925
       grind)
    | exact superpose eq1161925 eq11
    | exact resolve eq11 eq1161925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161925
  have eq1162004 : False := by grind
  exact eq1162004

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pyx_x_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
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
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
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
  have eq142 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
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
  have eq175 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq16 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op (M.op X1 X1) X0) (M.op X2 X2) X2
       have i₂ := eq16 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq574 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq576 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq580 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq574
       grind)
    | exact superpose eq574 eq40
    | exact resolve eq40 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq581 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq580
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq580
    | exact resolve eq580 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq583 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq581
    | exact resolve eq581 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq593 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq583 eq575
    | exact resolve eq575 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq583
  have eq600 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq593
       have r₂ := eq27
       grind)
    | exact resolve eq593 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq605 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq600 eq177
    | exact resolve eq177 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq610 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq600 eq605
    | exact resolve eq605 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600 eq605
  have eq613 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq610 eq142
    | exact resolve eq142 eq610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq610
  have eq616 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq613
    | exact resolve eq613 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq613
  have eq619 : x = (M.op x x) := by
    first
    | (have j1 := eq576 x
       grind)
    | (have r₁ := eq616
       have r₂ := eq576 x
       grind)
    | exact resolve eq616 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq623 : (k x x) = (M.op x x) := by
    first
    | (have i₁ := eq177 x
       have i₂ := eq619
       grind)
    | exact superpose eq619 eq177
    | exact resolve eq177 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq625 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 X1 x
       have i₂ := eq619
       grind)
    | exact superpose eq619 eq176
    | exact resolve eq176 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq627 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op x X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 x
       have i₂ := eq619
       grind)
    | exact superpose eq619 eq16
    | exact resolve eq16 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq628 : x = (k x x) := by
    first
    | (have i₁ := eq623
       have i₂ := eq619
       grind)
    | exact superpose eq619 eq623
    | exact resolve eq623 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619 eq623
  have eq630 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq628
       grind)
    | exact superpose eq628 eq40
    | exact resolve eq40 eq628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq628
  have eq633 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq630
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq630
    | exact resolve eq630 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq630
  have eq638 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq633 eq576
    | (have j0 := eq576 (σ x)
       grind)
    | (have r₁ := eq576 (σ x)
       have r₂ := eq633
       grind)
    | exact resolve eq576 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq639 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq638
  have eq646 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op (σ x) X0) := by
    intro X0 X1
    first
    | exact superpose eq639 eq176
    | exact resolve eq176 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq648 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (σ x) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq639 eq16
    | exact resolve eq16 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq654 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq639 eq625
    | exact resolve eq625 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq714 : (M.op x y) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq654 y
       grind)
    | exact superpose eq654 eq18
    | (have j1 := eq654 y
       grind)
    | exact resolve eq18 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq822 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X4 X4) X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq16 (M.op (M.op X4 X4) X1) X2 x
       have i₂ := eq175 X1 X0 x X4
       grind)
    | (have i₁ := eq16 (M.op (M.op X2 X2) X0) X1 X2
       have i₂ := eq175 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq823 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 (M.op X2 X2) x
       have i₂ := eq175 X1 X0 X2 x
       grind)
    | (have i₁ := eq16 X0 (M.op X2 X2) X2
       have i₂ := eq175 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq836 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) = (k (M.op X2 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X2
       have i₂ := eq175 X2 X2 X0 X1
       grind)
    | (have i₁ := eq177 (M.op x x)
       have i₂ := eq175 (M.op x x) X1 x x
       grind)
    | exact superpose eq175 eq177
    | exact resolve eq177 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq847 : ∀ X1 X2 : G, (M.op x (M.op (M.op X1 X1) X2)) = (k (M.op X2 X2) X2) := by
    intro X1 X2
    first
    | (have i₁ := eq836 x X1 X2
       have i₂ := eq625 (M.op (M.op X1 X1) X2) x
       grind)
    | exact superpose eq625 eq836
    | exact resolve eq836 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq856 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq823 X0 X1 x
       have i₂ := eq625 (M.op X0 (M.op X0 X1)) x
       grind)
    | exact superpose eq625 eq823
    | exact resolve eq823 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq857 : ∀ X0 X1 X2 : G, (M.op x X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq822 X0 X1 X2 x
       have i₂ := eq625 X1 x
       grind)
    | exact superpose eq625 eq822
    | exact resolve eq822 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq902 : ∀ X1 X2 : G, (k (M.op X2 X2) X2) = (M.op (σ x) (M.op (M.op X1 X1) X2)) := by
    intro X1 X2
    first
    | (have i₁ := eq847 X1 X2
       have i₂ := eq654 (M.op (M.op X1 X1) X2)
       grind)
    | exact superpose eq654 eq847
    | exact resolve eq847 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq910 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq856 X0 X1
       have i₂ := eq654 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq654 eq856
    | exact resolve eq856 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq911 : ∀ X0 X1 X2 : G, (M.op (σ x) X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq857 X0 X1 X2
       have i₂ := eq654 X1
       grind)
    | exact superpose eq654 eq857
    | exact resolve eq857 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq951 : ∀ X2 : G, (k (M.op X2 X2) X2) = (M.op (σ x) (M.op x X2)) := by
    intro X2
    first
    | (have i₁ := eq902 x X2
       have i₂ := eq625 X2 x
       grind)
    | exact superpose eq625 eq902
    | exact resolve eq902 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902
  have eq990 : ∀ X2 : G, (k (M.op X2 X2) X2) = (M.op (σ x) (M.op (σ x) X2)) := by
    intro X2
    first
    | (have i₁ := eq951 X2
       have i₂ := eq654 X2
       grind)
    | exact superpose eq654 eq951
    | exact resolve eq951 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq1134 : (σ y) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq910
    | (have j0 := eq910 (σ x) (σ y)
       grind)
    | exact resolve eq910 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1136 : ∀ X0 : G, (M.op (σ x) (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq910 X0 X0
       have i₂ := eq177 X0
       grind)
    | exact superpose eq177 eq910
    | exact resolve eq910 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq1138 : ∀ X0 X1 : G, (M.op (σ x) (k (M.op X0 X1) X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq910 X0 X1
       have i₂ := eq28 (M.op X0 X1) X0
       grind)
    | exact superpose eq28 eq910
    | (have j1 := eq28 X0 X0
       grind)
    | exact resolve eq910 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1150 : ∀ X0 X1 : G, (M.op (σ x) (k (k X1 X0) X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq28 eq1138
    | (have j0 := eq1138 X0 X1
       have j1 := eq28 X0 X0
       grind)
    | exact resolve eq1138 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138
  have eq1152 : (σ y) = (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq990 eq1134
    | exact resolve eq1134 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990 eq1134
  have eq1225 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq627 X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq627
    | (have j0 := eq627 X0 y
       grind)
    | exact resolve eq627 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq627
  have eq1332 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X1) (M.op X2 (M.op x y)))) = (M.op X2 y) := by
    intro X0 X1 X2
    first
    | exact superpose eq1225 eq175
    | exact resolve eq175 eq1225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq1333 : ∀ X0 : G, y = (k (M.op X0 (M.op x y)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq1225 eq28
    | (have j0 := eq28 X0 X0
       grind)
    | exact resolve eq28 eq1225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1349 : ∀ X0 : G, y = (k (k (M.op x y) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq1333
    | (have j0 := eq1333 X0
       have j1 := eq28 X0 X0
       grind)
    | exact resolve eq1333 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1333
  have eq1350 : ∀ X1 X2 : G, (M.op X2 y) = (M.op x (M.op (M.op X1 X1) (M.op X2 (M.op x y)))) := by
    intro X1 X2
    first
    | (have i₁ := eq1332 X1 X1 X2
       have i₂ := eq625 (M.op (M.op X1 X1) (M.op X2 sF0)) X1
       grind)
    | exact superpose eq625 eq1332
    | exact resolve eq1332 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332
  have eq1368 : ∀ X1 X2 : G, (M.op X2 y) = (M.op (σ x) (M.op (M.op X1 X1) (M.op X2 (M.op x y)))) := by
    intro X1 X2
    first
    | (have i₁ := eq1350 X1 X2
       have i₂ := eq654 (M.op (M.op X1 X1) (M.op X2 sF0))
       grind)
    | exact superpose eq654 eq1350
    | exact resolve eq1350 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1350
  have eq1380 : ∀ X2 : G, (M.op X2 y) = (M.op (σ x) (M.op x (M.op X2 (M.op x y)))) := by
    intro X2
    first
    | (have i₁ := eq1368 x X2
       have i₂ := eq625 (M.op X2 sF0) x
       grind)
    | exact superpose eq625 eq1368
    | exact resolve eq1368 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625 eq1368
  have eq1390 : ∀ X2 : G, (M.op X2 y) = (M.op (σ x) (M.op (σ x) (M.op X2 (M.op x y)))) := by
    intro X2
    first
    | (have i₁ := eq1380 X2
       have i₂ := eq654 (M.op X2 sF0)
       grind)
    | exact superpose eq654 eq1380
    | exact resolve eq1380 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654 eq1380
  have eq1802 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (k (M.op X0 X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq1136 eq648
    | exact resolve eq648 eq1136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1807 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq648
    | (have j0 := eq648 X0 (σ y)
       grind)
    | exact resolve eq648 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2054 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (σ x) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq1807 eq910
    | exact resolve eq910 eq1807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1807
  have eq3612 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 (M.op x y))) = (M.op X1 (M.op X1 (M.op X0 y))) := by
    intro X0 X1
    first
    | exact superpose eq1390 eq648
    | exact resolve eq648 eq1390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648 eq1390
  have eq8173 : (σ y) = (k (σ (k (M.op x y) y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1349 eq41
    | (have j1 := eq1349 y
       grind)
    | exact resolve eq41 eq1349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1349
  have eq8184 : (σ y) = (k (k (σ (M.op x y)) (σ y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq8173
       have i₂ := eq41 sF0
       grind)
    | exact superpose eq41 eq8173
    | exact resolve eq8173 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8173
  have eq8197 : (σ y) = (k (k (σ (M.op x y)) (σ y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq8184
    | exact resolve eq8184 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8184
  have eq8204 : (σ y) = (k (k (σ (M.op x y)) (σ y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq8197
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8197
    | exact resolve eq8197 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8197
  have eq27817 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq8204 eq1150
    | (have j0 := eq1150 (σ y) x
       grind)
    | exact resolve eq1150 eq8204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150 eq8204
  have eq27885 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq27817
    | exact resolve eq27817 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27817
  have eq27938 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq27885
       have r₂ := eq27
       grind)
    | exact resolve eq27885 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27885
  have eq27969 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27938 eq2054
    | exact resolve eq2054 eq27938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27993 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27938 eq910
    | exact resolve eq910 eq27938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq28011 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2054 eq27993
    | exact resolve eq27993 eq2054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2054 eq27993
  have eq28026 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq27969
    | exact resolve eq27969 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27969
  have eq28049 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28011 eq28026
    | exact resolve eq28026 eq28011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28011 eq28026
  have eq28125 : (k y y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1802 y y
       have i₂ := eq28049
       grind)
    | exact superpose eq28049 eq1802
    | exact resolve eq1802 eq28049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1802
  have eq28139 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28049 eq28125
    | exact resolve eq28125 eq28049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28049 eq28125
  have eq28258 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq28139
       grind)
    | exact superpose eq28139 eq41
    | exact resolve eq41 eq28139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq28139
  have eq28268 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28258
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq28258
    | exact resolve eq28258 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28258
  have eq28544 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28268 eq576
    | (have j0 := eq576 (σ y)
       grind)
    | (have r₁ := eq576 (σ y)
       have r₂ := eq28268
       grind)
    | exact resolve eq576 eq28268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28547 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28544
  have eq28597 : (σ y) = (M.op (σ x) (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28547 eq1136
    | exact resolve eq1136 eq28547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136 eq28547
  have eq28625 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28268 eq28597
    | exact resolve eq28597 eq28268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28268 eq28597
  have eq28656 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28625
    | exact resolve eq28625 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq28625
  have eq28657 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28656
  have eq28682 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq28657 eq27
    | exact resolve eq27 eq28657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq28683 : (σ y) = (k (M.op (σ y) (σ y)) (σ y)) := by
    first
    | exact superpose eq28657 eq1152
    | exact resolve eq1152 eq28657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152 eq28657
  have eq28727 : (τ (σ y)) = (k (τ (M.op (σ y) (σ y))) y) := by
    first
    | exact superpose eq28683 eq153
    | exact resolve eq153 eq28683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq28683
  have eq28731 : y = (k (τ (M.op (σ y) (σ y))) y) := by
    first
    | exact superpose eq32 eq28727
    | exact resolve eq28727 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28727
  have eq28918 : y = (k (τ (σ y)) y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27938 eq28731
    | exact resolve eq28731 eq27938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27938 eq28731
  have eq28933 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq32 eq28918
    | exact resolve eq28918 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq28918
  have eq28939 : y = (M.op y y) := by
    first
    | (have j1 := eq576 y
       grind)
    | (have r₁ := eq28933
       have r₂ := eq576 y
       grind)
    | exact resolve eq28933 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576 eq28933
  have eq28966 : ∀ X0 : G, (M.op (σ x) X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq646 X0 y
       have i₂ := eq28939
       grind)
    | exact superpose eq28939 eq646
    | exact resolve eq646 eq28939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq28978 : ∀ X0 : G, (M.op (σ x) y) = (M.op X0 (M.op X0 (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq911 y y X0
       have i₂ := eq28939
       grind)
    | exact superpose eq28939 eq911
    | exact resolve eq911 eq28939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911 eq28939
  have eq28994 : (M.op (σ x) y) = (M.op (σ x) (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq28978 x
       have i₂ := eq3612 y x
       grind)
    | exact superpose eq3612 eq28978
    | exact resolve eq28978 eq3612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3612 eq28978
  have eq29027 : (M.op (σ x) y) = (M.op (σ x) (M.op (σ x) (M.op x y))) := by
    first
    | (have i₁ := eq28994
       have i₂ := eq28966 sF0
       grind)
    | exact superpose eq28966 eq28994
    | exact resolve eq28994 eq28966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28966 eq28994
  have eq29047 : y = (M.op (σ x) y) := by
    first
    | exact superpose eq1225 eq29027
    | exact resolve eq29027 eq1225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225 eq29027
  have eq29061 : y = (M.op x y) := by
    first
    | exact superpose eq714 eq29047
    | exact resolve eq29047 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714 eq29047
  have eq31116 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq29061
       grind)
    | exact superpose eq29061 eq24
    | exact resolve eq24 eq29061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq29061
  have eq31193 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq31116 eq20
    | exact resolve eq20 eq31116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq31116
  have eq31212 : False := by grind
  exact eq31212

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pxx_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq9 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X1) X0) (M.op X2 X2) X2
       have i₂ := eq9 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq42 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq42 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq42 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq45 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq43 (σ X0)
       grind)
    | exact superpose eq43 eq15
    | exact resolve eq15 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq43 (τ X0)
       grind)
    | exact superpose eq43 eq18
    | exact resolve eq18 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq47
    | exact resolve eq47 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq52 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq45 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq45
    | exact resolve eq45 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq50 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq50
    | exact resolve eq50 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq68 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq75 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq76 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq77 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq73 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq73 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq79 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq75 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq75 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq82 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq76 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq76 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq76 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq93 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       have j1 := eq77 X0 X1
       grind)
    | (have r₁ := eq82 X0 X1
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq82 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq82
  have eq99 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq93
    | (have j0 := eq93 X0 X1
       grind)
    | exact resolve eq93 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq93
  have eq127 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X3 (M.op X1 X1) X2
       have i₂ := eq24 (M.op X1 X1) X0 X1
       grind)
    | (have i₁ := eq24 X3 (M.op X1 X1) X2
       have i₂ := eq24 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq10
    | exact resolve eq10 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq233 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq79 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq79 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq313 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq99 (σ X0) (σ X1)
       grind)
    | exact superpose eq99 eq15
    | (have j1 := eq99 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq313 X0 X1
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq313
    | (have j0 := eq313 X0 X1
       grind)
    | exact resolve eq313 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313
  have eq380 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X4 (M.op X4 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq23 X1 X4 x x
       have i₂ := eq23 X1 X0 x x
       grind)
    | (have i₁ := eq23 X0 X1 x x
       have i₂ := eq23 X0 (M.op x x) x x
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq395 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) (M.op (M.op X2 X2) X3)) ∨ (M.op X0 X3) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X3 X0 X1 X2
       have i₂ := eq99 X0 X3
       grind)
    | (have i₁ := eq23 X0 X0 X2 X3
       have i₂ := eq99 X0 X1
       grind)
    | exact superpose eq99 eq23
    | (have j1 := eq99 X0 X3
       grind)
    | exact resolve eq23 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X2 X2) x
       have i₂ := eq23 X1 X0 X2 x
       grind)
    | (have i₁ := eq9 X0 (M.op X2 X2) X2
       have i₂ := eq23 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq654 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0))) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq410 X0 X2 X1
       have i₂ := eq99 X0 X2
       grind)
    | (have i₁ := eq410 X0 X0 X2
       have i₂ := eq99 X0 X1
       grind)
    | exact superpose eq99 eq410
    | (have j1 := eq99 X0 X2
       grind)
    | exact resolve eq410 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq705 : ∀ X0 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ X0 = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq654 X0 x X2
       have i₂ := eq410 X0 X0 x
       grind)
    | exact superpose eq410 eq654
    | (have j0 := eq654 X0 x X2
       grind)
    | exact resolve eq654 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq766 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq705 (τ X0) X1
       grind)
    | exact superpose eq705 eq18
    | (have j1 := eq705 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq705
  have eq2210 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (k (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq233 (M.op X1 X1) (M.op X0 X0)
       grind)
    | (have r₁ := eq233 (M.op X1 X1) (M.op x x)
       have r₂ := eq24 (M.op X1 X1) X1 x
       grind)
    | (have r₁ := eq233 (M.op x x) (M.op X1 X1)
       have r₂ := eq24 (M.op x x) X1 x
       grind)
    | exact resolve eq233 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2344 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq234 (M.op X0 X0) (M.op X1 X1)
       grind)
    | (have r₁ := eq234 (M.op X1 X1) (M.op x x)
       have r₂ := eq24 (M.op X1 X1) X1 x
       grind)
    | (have r₁ := eq234 (M.op x x) (M.op X1 X1)
       have r₂ := eq24 (M.op x x) X1 x
       grind)
    | exact resolve eq234 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq234
  have eq12517 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq766 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq766
    | exact resolve eq766 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq12595 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12517 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq12517
    | (have j0 := eq12517 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq12517 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12517
  have eq35702 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) X2) = (M.op (M.op (M.op X3 X3) (M.op X0 (M.op X0 X0))) X2) ∨ (M.op X0 (M.op X4 X4)) = (k (M.op X4 X4) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq127 X3 (M.op (M.op X4 X4) (M.op X4 X4)) X1 X2
       have i₂ := eq395 X0 (M.op X4 X4) X4 (M.op X4 X4)
       grind)
    | exact superpose eq395 eq127
    | (have j1 := eq395 X0 X1 X2 (M.op X4 X4)
       grind)
    | exact resolve eq127 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq395
  have eq35929 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 X1) X2) = (M.op X0 X2) ∨ (M.op X0 (M.op X4 X4)) = (k (M.op X4 X4) X0) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq35702 X0 X1 X2 x X4
       have i₂ := eq410 X0 X0 x
       grind)
    | exact superpose eq410 eq35702
    | (have j0 := eq35702 X0 X1 X2 x X4
       grind)
    | exact resolve eq35702 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35702
  have eq106197 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X0)) ≠ (k (M.op X0 X0) (M.op X1 X1)) ∨ (M.op X2 (M.op X0 X0)) = (k (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq233 (M.op X0 X0) X2
       have i₂ := eq2344 X0 X1
       grind)
    | exact superpose eq2344 eq233
    | (have j0 := eq233 (M.op X0 X0) X2
       grind)
    | exact resolve eq233 eq2344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233 eq2344
  have eq106808 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X0 X0)) ≠ (M.op X2 (M.op X0 X0)) ∨ (M.op X2 (M.op X0 X0)) = (k (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq106197 X0 X1 X2
       have i₂ := eq2210 X1 X0
       grind)
    | exact superpose eq2210 eq106197
    | (have j0 := eq106197 X0 X1 X2
       grind)
    | (have r₁ := eq106197 X1 X0 (M.op X0 X0)
       have r₂ := eq2210 X0 X1
       grind)
    | exact resolve eq106197 eq2210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2210 eq106197
  have eq107105 : ∀ X0 X2 : G, (M.op X2 (M.op X0 X0)) = (k (M.op X0 X0) X2) := by
    intro X0 X2
    first
    | (have j0 := eq106808 X0 x X2
       have j1 := eq35929 X2 x X2 X0
       grind)
    | (have r₁ := eq106808 X0 x X0
       have r₂ := eq35929 X0 x (M.op X0 X0) x
       grind)
    | (have r₁ := eq106808 X0 x (M.op x x)
       have r₂ := eq35929 (M.op x x) x (M.op X0 X0) x
       grind)
    | exact resolve eq106808 eq35929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35929 eq106808
  have eq109750 : ∀ X0 X1 : G, (k (σ (M.op X0 X0)) X1) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq107105 (σ X0) x
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq107105
    | exact resolve eq107105 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109765 : ∀ X0 X1 : G, (k (τ (M.op X0 X0)) X1) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq107105 (τ X0) x
       have i₂ := eq194 X0
       grind)
    | exact superpose eq194 eq107105
    | exact resolve eq107105 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq109813 : ∀ X0 X1 : G, (k (τ (M.op X1 X1)) X0) = (τ (M.op (σ X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op X1 X1) X0
       have i₂ := eq107105 X1 (σ X0)
       grind)
    | exact superpose eq107105 eq22
    | exact resolve eq22 eq107105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq110665 : ∀ X0 X1 : G, (k (M.op X1 X1) (τ X0)) = (τ (M.op X0 (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 (M.op X1 X1) X0
       have i₂ := eq109750 X1 X0
       grind)
    | exact superpose eq109750 eq30
    | exact resolve eq30 eq109750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq109750
  have eq110692 : ∀ X0 X1 : G, (M.op (τ X0) (M.op X1 X1)) = (τ (M.op X0 (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq110665 X0 X1
       have i₂ := eq107105 X1 (τ X0)
       grind)
    | exact superpose eq107105 eq110665
    | exact resolve eq110665 eq107105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107105 eq110665
  have eq113162 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 (σ X1)))) = (k (τ (M.op (σ X1) (σ X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq109813 X1 (σ X1)
       have i₂ := eq380 (σ X1) (σ X1) X0
       grind)
    | (have i₁ := eq109813 X1 (σ X1)
       have i₂ := eq380 X0 (σ X1) (σ X1)
       grind)
    | exact superpose eq380 eq109813
    | exact resolve eq109813 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380 eq109813
  have eq113280 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 (σ X1)))) = (M.op X1 (τ (M.op (σ X1) (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq113162 X0 X1
       have i₂ := eq109765 (σ X1) X1
       grind)
    | exact superpose eq109765 eq113162
    | exact resolve eq113162 eq109765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109765 eq113162
  have eq113422 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 (σ X1)))) = (M.op X1 (τ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq113280 X0 X1
       have i₂ := eq52 X1
       grind)
    | exact superpose eq52 eq113280
    | exact resolve eq113280 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113280
  have eq113511 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (τ (M.op X0 (M.op X0 (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq113422 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq113422
    | exact resolve eq113422 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113422
  have eq115271 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (τ (M.op X0 (M.op X0 (σ X1))))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq410 X1 X1 X2
       have i₂ := eq113511 X0 X1
       grind)
    | exact superpose eq113511 eq410
    | exact resolve eq410 eq113511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113511
  have eq120564 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (τ (M.op (σ X0) (σ (M.op X0 X0))))) = X2 ∨ (σ (k X2 X0)) = (M.op (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq115271 (σ X0) X2 X1
       have i₂ := eq324 X0 X2
       grind)
    | exact superpose eq324 eq115271
    | (have j1 := eq324 X0 X2
       grind)
    | exact resolve eq115271 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324 eq115271
  have eq120945 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (τ (σ X0)) (M.op X0 X0))) = X2 ∨ (σ (k X2 X0)) = (M.op (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq120564 X0 X1 X2
       have i₂ := eq110692 (σ X0) X0
       grind)
    | exact superpose eq110692 eq120564
    | (have j0 := eq120564 X0 X1 X2
       grind)
    | exact resolve eq120564 eq110692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110692 eq120564
  have eq120993 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0))) = X2 ∨ (σ (k X2 X0)) = (M.op (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq120945 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq120945
    | (have j0 := eq120945 X0 X1 X2
       grind)
    | exact resolve eq120945 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120945
  have eq121001 : ∀ X0 X2 : G, (σ (k X2 X0)) = (M.op (σ X0) (σ X2)) ∨ X0 = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq120993 X0 x X2
       have i₂ := eq410 X0 X0 x
       grind)
    | exact superpose eq410 eq120993
    | (have j0 := eq120993 X0 x X2
       grind)
    | exact resolve eq120993 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq120993
  have eq141381 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq121001 x y
       grind)
    | exact superpose eq121001 eq16
    | (have j1 := eq121001 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq121001 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq121001 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq121001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121001
  have eq141521 : x = y := by
    first
    | (have j1 := eq12595 x y
       grind)
    | (have r₁ := eq141381
       have r₂ := eq12595 x y
       grind)
    | (have r₁ := eq141381
       have r₂ := eq12595 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq141381
       have r₂ := eq12595 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq141381 eq12595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12595 eq141381
  have eq141876 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq141521
       grind)
    | exact superpose eq141521 eq16
    | exact resolve eq16 eq141521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141521
  have eq141877 : False := by grind
  exact eq141877
