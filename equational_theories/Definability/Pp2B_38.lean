import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_x_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op (M.op (M.op y (M.op x y)) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : x ≠ (M.op x y) ∨ (k y x) = (M.op y x) := by
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
  have eq64 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X1)) X2) ≠ X0 ∨ (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       grind)
    | (have r₁ := eq13 (M.op (M.op X1 (M.op X2 X1)) X2) (M.op (M.op X1 (M.op X2 X1)) X2)
       have r₂ := eq14 (M.op (M.op X1 (M.op X2 X1)) X2) X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq75 : x ≠ (M.op x y) ∨ y = (M.op y x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq94 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq95 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100
    | exact resolve eq100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq114
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114
    | exact resolve eq114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq625 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X1) X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))
       have i₂ := eq52 X1 X0 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq645 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq14 X2 x (M.op X0 X0)
       have i₂ := eq625 x X0 (M.op X0 X0)
       grind)
    | exact superpose eq625 eq14
    | exact resolve eq14 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq791 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq13 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq792 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ X0) (σ (k X0 X1))) (σ X1)) X2) = X2 ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (σ X0) (σ X1)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq14
    | (have j1 := eq93 X0 X1
       grind)
    | exact resolve eq14 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq803 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq791 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq791 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq791 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq791 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791
  have eq814 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq803 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq803
    | (have j0 := eq803 X0 X1
       grind)
    | exact resolve eq803 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq899 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X0)) ≠ X2 ∨ (M.op X2 (M.op X0 (M.op (M.op X1 X1) X0))) = (k X2 (M.op X0 (M.op (M.op X1 X1) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X0 (M.op X0 X0) (M.op X1 (M.op (M.op X0 X0) X1))
       have i₂ := eq52 X0 X1 (M.op X0 X0) (M.op X1 (M.op (M.op X0 X0) X1))
       grind)
    | exact superpose eq52 eq65
    | (have r₁ := eq65 (M.op X1 (M.op (M.op X0 X0) X1)) (M.op X0 X0) (M.op X1 (M.op (M.op X0 X0) X1))
       have r₂ := eq52 X0 X1 (M.op X0 X0) (M.op X1 (M.op (M.op X0 X0) X1))
       grind)
    | (have r₁ := eq65 (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) (M.op (M.op X1 (M.op X2 X1)) X2)) X1 X2
       have r₂ := eq52 X0 X1 X2 (M.op (M.op X1 (M.op X2 X1)) X2)
       grind)
    | exact resolve eq65 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq901 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X1 X0)) X1) (M.op (M.op X0 (M.op X1 X0)) X1)) = (k (M.op (M.op X0 (M.op X1 X0)) X1) (M.op (M.op X0 (M.op X1 X0)) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq65 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq902 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X1) = (k (M.op (M.op X0 (M.op X1 X0)) X1) (M.op (M.op X0 (M.op X1 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq901 X0 X1
       have i₂ := eq14 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
       grind)
    | exact superpose eq14 eq901
    | exact resolve eq901 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq903 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X2 ∨ (M.op X2 (M.op X0 (M.op (M.op X1 X1) X0))) = (k X2 (M.op X0 (M.op (M.op X1 X1) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq899 X0 X1 X2
       have i₂ := eq645 X1 X0
       grind)
    | (have i₁ := eq899 X0 X1 X2
       have i₂ := eq645 X0 (M.op (M.op X1 X1) X0)
       grind)
    | exact superpose eq645 eq899
    | (have j0 := eq899 X0 X1 X2
       grind)
    | (have r₁ := eq899 (M.op X0 X0) X1 (M.op (M.op X1 X1) (M.op X0 X0))
       have r₂ := eq645 X0 (M.op (M.op X1 X1) (M.op X0 X0))
       grind)
    | (have r₁ := eq899 X0 X1 (M.op (M.op X0 X0) (M.op X0 (M.op (M.op X1 X1) X0)))
       have r₂ := eq645 X0 (M.op X0 (M.op (M.op X1 X1) X0))
       grind)
    | exact resolve eq899 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq914 : ∀ X0 X2 : G, (M.op X0 X0) ≠ X2 ∨ (M.op X2 (M.op X0 X0)) = (k X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq903 X2 X0 X2
       have i₂ := eq645 X0 X2
       grind)
    | (have i₁ := eq903 X0 x X2
       have i₂ := eq645 X0 (M.op (M.op x x) X0)
       grind)
    | exact superpose eq645 eq903
    | (have j0 := eq903 X0 x X2
       grind)
    | (have r₁ := eq903 (M.op X0 X0) x (M.op X0 X0)
       have r₂ := eq645 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq903 X0 x (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq645 X0 (M.op X0 X0)
       grind)
    | exact resolve eq903 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq3523 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq914 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914
  have eq3525 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3523 X0
       have i₂ := eq645 X0 (M.op X0 X0)
       grind)
    | (have i₁ := eq3523 X0
       have i₂ := eq645 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq645 eq3523
    | exact resolve eq3523 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3523
  have eq5474 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq94 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq94
    | (have j0 := eq94 x
       grind)
    | exact resolve eq94 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq5487 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5474
  have eq5493 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5487
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq5487
    | exact resolve eq5487 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq5487
  have eq5511 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq5493
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq5493 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5493
  have eq5515 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5511 eq49
    | exact resolve eq49 eq5511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq5511
  have eq5665 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq95 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq95
    | (have j0 := eq95 y
       grind)
    | exact resolve eq95 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq5677 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5665
  have eq5682 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5677
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq5677
    | exact resolve eq5677 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq5677
  have eq5707 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq5682
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq5682 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5682
  have eq5729 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq5707 eq87
    | exact resolve eq87 eq5707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq5707
  have eq10916 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10917 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq10916
    | exact resolve eq10916 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10916
  have eq10928 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq10917
       have r₂ := eq27
       grind)
    | exact resolve eq10917 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10917
  have eq10930 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq10928
    | exact resolve eq10928 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10928
  have eq10932 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq10930 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq10930
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq10930
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq10930
       grind)
    | exact resolve eq12 eq10930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10930
  have eq10944 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq10932
  have eq10955 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq10944
    | exact resolve eq10944 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10944
  have eq10956 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq10955
  have eq12117 : (τ (σ y)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq10956 eq82
    | exact resolve eq82 eq10956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq12118 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq10956 eq115
    | exact resolve eq115 eq10956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10956
  have eq12131 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12118
  have eq12140 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq12117
    | exact resolve eq12117 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12117
  have eq12143 : y ≠ y ∨ x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq12131
       grind)
    | exact superpose eq12131 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq12131
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq12131
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq12131
       grind)
    | exact resolve eq12 eq12131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12144 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq12131
       grind)
    | exact superpose eq12131 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq12131
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq12131
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq12131
       grind)
    | exact resolve eq13 eq12131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12131
  have eq12154 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12144
  have eq12155 : x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12143
  have eq12165 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12154
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12154
    | exact resolve eq12154 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12154
  have eq12166 : x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12155
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12155
    | exact resolve eq12155 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12155
  have eq12167 : y = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12166
  have eq12173 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq12165
       grind)
    | exact superpose eq12165 eq44
    | exact resolve eq44 eq12165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12165
  have eq12195 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq12173
    | exact resolve eq12173 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12173
  have eq12210 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq12167
       grind)
    | exact superpose eq12167 eq72
    | exact resolve eq72 eq12167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12167
  have eq12233 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12210
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12210
    | exact resolve eq12210 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12210
  have eq13524 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12233 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq12233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12233
  have eq13528 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13524
    | exact resolve eq13524 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13524
  have eq13541 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13528
    | exact resolve eq13528 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13528
  have eq13542 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq13541
  have eq13558 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq12140
       grind)
    | exact superpose eq12140 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq12140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12140
  have eq13559 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13558
  have eq13562 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13559
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13559
    | exact resolve eq13559 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13559
  have eq13576 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13562
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13562
    | exact resolve eq13562 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13562
  have eq13577 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13576
  have eq13685 : y ≠ y ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq13577
       grind)
    | exact superpose eq13577 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq13577
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq13577
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq13577
       grind)
    | exact resolve eq13 eq13577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13577
  have eq13695 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13685
  have eq13706 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13695
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13695
    | exact resolve eq13695 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13695
  have eq13723 : (σ y) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq814 x y
       have i₂ := eq13706
       grind)
    | exact superpose eq13706 eq814
    | (have j0 := eq814 x y
       grind)
    | exact resolve eq814 eq13706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13706
  have eq13729 : (σ y) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq13723
    | exact resolve eq13723 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13723
  have eq13741 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13729
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13729
    | exact resolve eq13729 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13729
  have eq13748 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq13741
    | exact resolve eq13741 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13741
  have eq13753 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13748
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13748
    | exact resolve eq13748 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13748
  have eq13759 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13753
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13753
    | exact resolve eq13753 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13753
  have eq13764 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13759
    | exact resolve eq13759 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13759
  have eq13771 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq13764
       have r₂ := eq27
       grind)
    | exact resolve eq13764 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13764
  have eq13776 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13771
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13771
    | exact resolve eq13771 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13771
  have eq13779 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13776
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13776
    | exact resolve eq13776 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13776
  have eq13780 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13779
    | exact resolve eq13779 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13779
  have eq13781 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq13780
  have eq15753 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13542 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq13542
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq13542
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq13542
       grind)
    | exact resolve eq13 eq13542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13542
  have eq15763 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq15753
  have eq15774 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq15763
    | exact resolve eq15763 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15763
  have eq16032 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq15774 eq12195
    | exact resolve eq12195 eq15774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12195 eq15774
  have eq16041 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16032
  have eq16045 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16041
       have r₂ := eq27
       grind)
    | exact resolve eq16041 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16041
  have eq16051 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ y)) (σ x)) X0) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16045 eq51
    | exact resolve eq51 eq16045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq16045
  have eq16073 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16051 X0
       have i₂ := eq645 sF3 sF2
       grind)
    | (have i₁ := eq16051 X0
       have i₂ := eq645 X0 (M.op (M.op sF3 sF3) sF2)
       grind)
    | exact superpose eq645 eq16051
    | exact resolve eq16051 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16051
  have eq16227 : (τ (σ x)) = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16073 eq5515
    | exact resolve eq5515 eq16073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5515 eq16073
  have eq16323 : x = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq16227
    | exact resolve eq16227 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16227
  have eq16597 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq16323
       grind)
    | exact superpose eq16323 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq16323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16323
  have eq16598 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16597
  have eq16690 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq645 x X0
       have i₂ := eq16598
       grind)
    | exact superpose eq16598 eq645
    | exact resolve eq645 eq16598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16598
  have eq17089 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq16690 y
       grind)
    | exact superpose eq16690 eq18
    | (have j1 := eq16690 y
       grind)
    | exact resolve eq18 eq16690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16690
  have eq17178 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17089
       have r₂ := eq13781
       grind)
    | exact resolve eq17089 eq13781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13781 eq17089
  have eq17500 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17178 eq27
    | exact resolve eq27 eq17178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17502 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17178 eq64
    | (have r₁ := eq64
       have r₂ := eq17178
       grind)
    | exact resolve eq64 eq17178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq17503 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17178 eq76
    | (have r₁ := eq76
       have r₂ := eq17178
       grind)
    | exact resolve eq76 eq17178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq17510 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq17503
  have eq17511 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq17502
  have eq18943 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17511 eq115
    | exact resolve eq115 eq17511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq17511
  have eq18963 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq18943
  have eq19131 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17510 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq17510
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq17510
       grind)
    | exact resolve eq13 eq17510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17510
  have eq19144 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq19131
  have eq19160 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq19144
    | exact resolve eq19144 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19144
  have eq20956 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq19160
  have eq20961 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20956
       have r₂ := eq17178
       grind)
    | exact resolve eq20956 eq17178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17178 eq20956
  have eq20973 : (τ (σ x)) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20961 eq57
    | exact resolve eq57 eq20961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq20961
  have eq21015 : x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq20973
    | exact resolve eq20973 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq20973
  have eq21467 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq21015
       grind)
    | exact superpose eq21015 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq21015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21489 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21467
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21467
    | exact resolve eq21467 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21467
  have eq21490 : y = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq21489
  have eq22792 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq21490
       grind)
    | exact superpose eq21490 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq21490
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq21490
       grind)
    | exact resolve eq13 eq21490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21490
  have eq22807 : (M.op x y) = (k x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq22792
  have eq22823 : (M.op x y) = (k x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq22807
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22807
    | exact resolve eq22807 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22807
  have eq22854 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21015
       have i₂ := eq22823
       grind)
    | exact superpose eq22823 eq21015
    | exact resolve eq21015 eq22823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22823
  have eq22863 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq22854
  have eq22957 : (M.op (M.op x x) y) = (k (M.op (M.op x x) y) (M.op (M.op x x) y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq902 x y
       have i₂ := eq22863
       grind)
    | exact superpose eq22863 eq902
    | exact resolve eq902 eq22863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902 eq22863
  have eq22967 : y = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22957
       have i₂ := eq645 x y
       grind)
    | (have i₁ := eq22957
       have i₂ := eq645 x (M.op (M.op x x) y)
       grind)
    | exact superpose eq645 eq22957
    | exact resolve eq22957 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22957
  have eq23009 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq814 y y
       have i₂ := eq22967
       grind)
    | exact superpose eq22967 eq814
    | (have j0 := eq814 y y
       grind)
    | exact resolve eq814 eq22967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22967
  have eq23014 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq23009
  have eq23015 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq23014
  have eq23026 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23015
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23015
    | exact resolve eq23015 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23015
  have eq23222 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23026 eq645
    | exact resolve eq645 eq23026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23026
  have eq23289 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23222 eq18963
    | exact resolve eq18963 eq23222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18963 eq23222
  have eq23366 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq23289
  have eq23425 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq23366
       have r₂ := eq17500
       grind)
    | exact resolve eq23366 eq17500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17500 eq23366
  have eq23461 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq23425
       grind)
    | exact superpose eq23425 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq23425
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq23425
       grind)
    | exact resolve eq13 eq23425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23425
  have eq23475 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq23461
  have eq23495 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq23475
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23475
    | exact resolve eq23475 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23475
  have eq23972 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21015
       have i₂ := eq23495
       grind)
    | exact superpose eq23495 eq21015
    | exact resolve eq21015 eq23495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21015 eq23495
  have eq23981 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq23972
  have eq24055 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23981 eq20
    | exact resolve eq20 eq23981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24057 : ∀ X0 : G, (M.op (M.op (M.op y y) x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23981 eq50
    | exact resolve eq50 eq23981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq23981
  have eq24176 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq24057 X0
       have i₂ := eq645 y x
       grind)
    | (have i₁ := eq24057 X0
       have i₂ := eq645 X0 (M.op (M.op y y) x)
       grind)
    | exact superpose eq645 eq24057
    | exact resolve eq24057 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24057
  have eq24178 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24055
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24055
    | exact resolve eq24055 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24055
  have eq24222 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24178 eq26
    | exact resolve eq26 eq24178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24178
  have eq24425 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3525 x
       have i₂ := eq24176 x
       grind)
    | exact superpose eq24176 eq3525
    | exact resolve eq3525 eq24176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3525 eq24176
  have eq24587 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq814 x x
       have i₂ := eq24425
       grind)
    | exact superpose eq24425 eq814
    | (have j0 := eq814 x x
       grind)
    | exact resolve eq814 eq24425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24425
  have eq24592 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq24587
  have eq24593 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq24592
  have eq24604 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24593
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24593
    | exact resolve eq24593 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24593
  have eq24653 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq24604 eq645
    | exact resolve eq645 eq24604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24604
  have eq24711 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24653 eq24222
    | exact resolve eq24222 eq24653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24222 eq24653
  have eq24783 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24711
  have eq24832 : x = (M.op x y) := by
    first
    | (have r₁ := eq24783
       have r₂ := eq27
       grind)
    | exact resolve eq24783 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24783
  have eq24862 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq24832 eq20
    | exact resolve eq20 eq24832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq24866 : x ≠ x ∨ (k y x) = (M.op y x) := by
    first
    | exact superpose eq24832 eq63
    | (have r₁ := eq63
       have r₂ := eq24832
       grind)
    | exact resolve eq63 eq24832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq24869 : x ≠ x ∨ y = (M.op y x) ∨ x = (k x y) := by
    first
    | exact superpose eq24832 eq75
    | (have r₁ := eq75
       have r₂ := eq24832
       grind)
    | exact resolve eq75 eq24832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq24924 : y = (M.op y x) ∨ x = (k x y) := by grind
  clear eq24869
  have eq24925 : (k y x) = (M.op y x) := by grind
  clear eq24866
  have eq24977 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq24862
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24862
    | exact resolve eq24862 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24862
  have eq25015 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq24977 eq26
    | exact resolve eq26 eq24977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25219 : (k (σ y) (σ x)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq24925
       grind)
    | exact superpose eq24925 eq72
    | exact resolve eq72 eq24925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq24925
  have eq25255 : (k (σ y) (σ (M.op x y))) = (σ (M.op y x)) := by
    first
    | exact superpose eq24977 eq25219
    | exact resolve eq25219 eq24977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25219
  have eq26883 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq24924
       grind)
    | exact superpose eq24924 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq24924
       grind)
    | exact resolve eq13 eq24924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24924
  have eq26897 : (M.op x y) = (k x y) ∨ x = (k x y) := by grind
  clear eq26883
  have eq26912 : (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq26897
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq26897
    | exact resolve eq26897 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq26897
  have eq26929 : x = (k x y) ∨ x = (k x y) := by
    first
    | exact superpose eq24832 eq26912
    | exact resolve eq26912 eq24832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24832 eq26912
  have eq26930 : x = (k x y) := by grind
  clear eq26929
  have eq27000 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq26930
       grind)
    | exact superpose eq26930 eq44
    | exact resolve eq44 eq26930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq27016 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ x)) (σ y)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq792 x y X0
       have i₂ := eq26930
       grind)
    | exact superpose eq26930 eq792
    | (have j0 := eq792 x y x
       grind)
    | exact resolve eq792 eq26930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq27018 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq814 x y
       have i₂ := eq26930
       grind)
    | exact superpose eq26930 eq814
    | (have j0 := eq814 x y
       grind)
    | exact resolve eq814 eq26930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814 eq26930
  have eq27022 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq27018
  have eq27034 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27022
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq27022
    | exact resolve eq27022 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27022
  have eq27036 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq27016 X0
       have i₂ := eq645 (σ x) (σ y)
       grind)
    | (have i₁ := eq27016 X0
       have i₂ := eq645 X0 (M.op (M.op (σ x) (σ x)) (σ y))
       grind)
    | exact superpose eq645 eq27016
    | exact resolve eq27016 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27016
  have eq27046 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq24977 eq27000
    | exact resolve eq27000 eq24977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27000
  have eq27051 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27034
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27034
    | exact resolve eq27034 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27034
  have eq27053 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq27036 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq27036
    | (have j0 := eq27036 X0
       grind)
    | exact resolve eq27036 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27036
  have eq27062 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq27046
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27046
    | exact resolve eq27046 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27046
  have eq27066 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24977 eq27051
    | exact resolve eq27051 eq24977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27051
  have eq27068 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq27053 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq27053
    | (have j0 := eq27053 X0
       grind)
    | exact resolve eq27053 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27053
  have eq27075 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq24977 eq27062
    | exact resolve eq27062 eq24977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27062
  have eq27079 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq27066
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq27066
    | exact resolve eq27066 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27066
  have eq27081 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq27068 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27068
    | (have j0 := eq27068 X0
       grind)
    | exact resolve eq27068 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27068
  have eq27089 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq27079
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27079
    | exact resolve eq27079 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27079
  have eq27091 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq27081
    | (have j0 := eq27081 X0
       grind)
    | exact resolve eq27081 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27081
  have eq27096 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq26 eq27089
    | exact resolve eq27089 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq27089
  have eq27098 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq24977 eq27091
    | (have j0 := eq27091 X0
       grind)
    | exact resolve eq27091 eq24977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27091
  have eq27103 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq24977 eq27096
    | exact resolve eq27096 eq24977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27096
  have eq27105 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq27098 X0
       grind)
    | (have r₁ := eq27098 X0
       have r₂ := eq27
       grind)
    | exact resolve eq27098 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27098
  have eq27110 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have r₁ := eq27103
       have r₂ := eq27
       grind)
    | exact resolve eq27103 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27103
  have eq27112 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq27105 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27105
    | (have j0 := eq27105 X0
       grind)
    | exact resolve eq27105 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27105
  have eq27118 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq24977 eq27112
    | (have j0 := eq27112 X0
       grind)
    | exact resolve eq27112 eq24977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27112
  have eq27124 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq27118 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq27118
    | (have j0 := eq27118 X0
       grind)
    | exact resolve eq27118 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq27118
  have eq27217 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq27124 (M.op x X0)
       grind)
    | exact superpose eq27124 eq13
    | (have j0 := eq13 (σ (M.op x y)) (σ y)
       have j1 := eq27124 X0
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (σ y)
       have r₂ := eq27124 X0
       grind)
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq27124 (σ y)
       grind)
    | exact resolve eq13 eq27124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27124
  have eq27232 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq27217 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27217
  have eq27247 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27075 eq27232
    | (have j0 := eq27232 X0
       grind)
    | exact resolve eq27232 eq27075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27075 eq27232
  have eq27256 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq25015 eq27247
    | (have j0 := eq27247 X0
       grind)
    | exact resolve eq27247 eq25015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27247
  have eq27261 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq27256 X0
       grind)
    | (have r₁ := eq27256 X0
       have r₂ := eq27
       grind)
    | exact resolve eq27256 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27256
  have eq27280 : (τ (σ y)) = (k y y) := by
    first
    | exact superpose eq27261 eq5729
    | exact resolve eq5729 eq27261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5729
  have eq27412 : y = (k y y) := by
    first
    | exact superpose eq29 eq27280
    | exact resolve eq27280 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq27280
  have eq27467 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq27412
       grind)
    | exact superpose eq27412 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq27412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27412
  have eq27482 : y = (M.op y y) := by grind
  clear eq27467
  have eq27529 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq645 y X0
       have i₂ := eq27482
       grind)
    | exact superpose eq27482 eq645
    | exact resolve eq645 eq27482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645 eq27482
  have eq28135 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq25255
       have i₂ := eq27529 x
       grind)
    | exact superpose eq27529 eq25255
    | exact resolve eq25255 eq27529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25255 eq27529
  have eq28254 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq28135
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28135
    | exact resolve eq28135 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq28135
  have eq28278 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq24977 eq28254
    | exact resolve eq28254 eq24977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24977 eq28254
  have eq28305 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq28278 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq11 eq28278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28278
  have eq28316 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by grind
  clear eq28305
  have eq28318 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq25015 eq28316
    | exact resolve eq28316 eq25015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25015 eq28316
  have eq28329 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq28318
       have r₂ := eq27
       grind)
    | exact resolve eq28318 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq28318
  have eq28340 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27261 eq28329
    | exact resolve eq28329 eq27261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27261 eq28329
  have eq28351 : False := by grind
  exact eq28351

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_y_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
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
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq37
  have eq75 : x ≠ (M.op x y) ∨ y = (M.op x x) ∨ x = (k y x) := by
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
  have eq76 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq112
    | exact resolve eq112 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq113
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq113
    | exact resolve eq113 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq816 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq94 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq7768 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq114 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7769 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq7768
    | exact resolve eq7768 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7768
  have eq7780 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq7769
       have r₂ := eq28
       grind)
    | exact resolve eq7769 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7769
  have eq7782 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq7780
    | exact resolve eq7780 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7780
  have eq7789 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq7782
  have eq7801 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq7789
    | exact resolve eq7789 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7789
  have eq8126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq7801 eq114
    | exact resolve eq114 eq7801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7801
  have eq8134 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8126
  have eq8136 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8134
       have r₂ := eq28
       grind)
    | exact resolve eq8134 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8134
  have eq8143 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8136
  have eq8157 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8143
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq8143
    | exact resolve eq8143 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8143
  have eq8254 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq8157
       grind)
    | exact superpose eq8157 eq72
    | exact resolve eq72 eq8157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8157
  have eq8268 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq8254
    | exact resolve eq8254 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8254
  have eq8332 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8268 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq8268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8335 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq8332
    | exact resolve eq8332 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8332
  have eq8346 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8335
       have r₂ := eq28
       grind)
    | exact resolve eq8335 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8335
  have eq8348 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq8346
    | exact resolve eq8346 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8346
  have eq8349 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8348
  have eq9008 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8349
  have eq9022 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq9008
    | exact resolve eq9008 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9008
  have eq9167 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9022 eq8268
    | exact resolve eq8268 eq9022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8268 eq9022
  have eq9170 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9167
  have eq9174 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9170
       have r₂ := eq28
       grind)
    | exact resolve eq9170 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9170
  have eq9176 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9174 eq28
    | exact resolve eq28 eq9174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9178 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9174 eq76
    | (have r₁ := eq76
       have r₂ := eq9174
       grind)
    | exact resolve eq76 eq9174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq9182 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq9178
  have eq10467 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq9182
  have eq10483 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq10467
    | exact resolve eq10467 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10467
  have eq11564 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq114 eq10483
    | exact resolve eq10483 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq11582 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq10483
  have eq11587 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq11564
  have eq11589 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11582
       have r₂ := eq9174
       grind)
    | exact resolve eq11582 eq9174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9174 eq11582
  have eq11591 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq11587
       have r₂ := eq9176
       grind)
    | exact resolve eq11587 eq9176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9176 eq11587
  have eq11593 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11591
       have r₂ := eq28
       grind)
    | exact resolve eq11591 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11591
  have eq11602 : (τ (σ x)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11589 eq83
    | exact resolve eq83 eq11589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq11589
  have eq11638 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq11602
    | exact resolve eq11602 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq11602
  have eq11650 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq11593
  have eq11666 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11650
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11650
    | exact resolve eq11650 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11650
  have eq11995 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11638
       have i₂ := eq11666
       grind)
    | exact superpose eq11666 eq11638
    | exact resolve eq11638 eq11666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11638 eq11666
  have eq12000 : x = (M.op x y) := by grind
  clear eq11995
  have eq12023 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq12000 eq21
    | exact resolve eq21 eq12000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq12029 : x ≠ x ∨ y = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq12000 eq75
    | (have r₁ := eq75
       have r₂ := eq12000
       grind)
    | exact resolve eq75 eq12000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq12080 : y = (M.op x x) ∨ x = (k y x) := by grind
  clear eq12029
  have eq12131 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq12023
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12023
    | exact resolve eq12023 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12023
  have eq12132 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq12131 eq27
    | exact resolve eq27 eq12131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17295 : (M.op x y) = (k y x) ∨ x = (k y x) := by grind
  clear eq12080
  have eq17315 : (M.op x y) = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq17295
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17295
    | exact resolve eq17295 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq17295
  have eq17326 : x = (k y x) ∨ x = (k y x) := by
    first
    | exact superpose eq12000 eq17315
    | exact resolve eq17315 eq12000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12000 eq17315
  have eq17327 : x = (k y x) := by grind
  clear eq17326
  have eq17333 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq17327
       grind)
    | exact superpose eq17327 eq72
    | exact resolve eq72 eq17327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq17345 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq816 x y
       have i₂ := eq17327
       grind)
    | exact superpose eq17327 eq816
    | (have j0 := eq816 x y
       grind)
    | exact resolve eq816 eq17327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816 eq17327
  have eq17348 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq17345
  have eq17355 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq17348
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq17348
    | exact resolve eq17348 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17348
  have eq17365 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq12131 eq17333
    | exact resolve eq17333 eq12131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17333
  have eq17367 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq17355
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17355
    | exact resolve eq17355 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17355
  have eq17377 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq17365
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17365
    | exact resolve eq17365 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17365
  have eq17378 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq17367
    | exact resolve eq17367 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq17367
  have eq17387 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq12131 eq17377
    | exact resolve eq17377 eq12131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17377
  have eq17388 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12131 eq17378
    | exact resolve eq17378 eq12131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17378
  have eq17392 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq17388
       have r₂ := eq28
       grind)
    | exact resolve eq17388 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17388
  have eq17396 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq17392
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17392
    | exact resolve eq17392 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq17392
  have eq17400 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq12131 eq17396
    | exact resolve eq17396 eq12131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12131 eq17396
  have eq17404 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq17400
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq17400
    | exact resolve eq17400 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq17400
  have eq17470 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq17404
  have eq17490 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq12132 eq17470
    | exact resolve eq17470 eq12132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12132 eq17470
  have eq17492 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17387 eq17490
    | exact resolve eq17490 eq17387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17387 eq17490
  have eq17493 : False := by grind
  exact eq17493

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_x_pxx_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq44 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq50 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       have i₂ := eq14 (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq37
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq89
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq89
    | exact resolve eq89 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq95
    | exact resolve eq95 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq456 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq63 (M.op X0 X0) x x X3
       have i₂ := eq62 X0 x x (M.op X0 X0)
       grind)
    | exact superpose eq62 eq63
    | exact resolve eq63 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq63
  have eq487 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq456 X0 (M.op X0 X0)
       grind)
    | exact superpose eq456 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq456 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq497 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq487 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq685 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq75 X0 X0
       grind)
    | exact superpose eq75 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq75 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq75 X1 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq75 X0 X1
       grind)
    | exact resolve eq13 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq75 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq698 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq697 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq706 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq685 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq709 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq706 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq706 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq706 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq2008 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq709 (τ X0) X1
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq709
    | (have j0 := eq709 (τ X0) X1
       grind)
    | exact resolve eq709 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq2040 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2008 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2008
    | (have j0 := eq2008 X0 X1
       grind)
    | exact resolve eq2008 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2008
  have eq2054 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2040 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2040
    | (have j0 := eq2040 X0 X1
       grind)
    | exact resolve eq2040 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040
  have eq5079 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq698 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq698
    | (have j0 := eq698 (τ X0)
       grind)
    | exact resolve eq698 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq5114 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5079 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5079
    | (have j0 := eq5079 X0
       grind)
    | exact resolve eq5079 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5079
  have eq5129 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5114 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5114
    | (have j0 := eq5114 X0
       grind)
    | exact resolve eq5114 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5114
  have eq29208 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq29209 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq29208
    | exact resolve eq29208 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29208
  have eq29220 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq29209
       have r₂ := eq28
       grind)
    | exact resolve eq29209 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29209
  have eq29229 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq29220 eq497
    | exact resolve eq497 eq29220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29220
  have eq29264 : ∀ X0 : G, x = (M.op y y) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq29229 X0
       have j1 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq29229 X0
       have r₂ := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq29229 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq29229 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29229
  have eq29274 : ∀ X0 X1 : G, (k X0 x) = X0 ∨ (k X1 (σ x)) = X1 ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq497 y X0
       have i₂ := eq29264 X1
       grind)
    | exact superpose eq29264 eq497
    | (have j1 := eq29264 X1
       grind)
    | exact resolve eq497 eq29264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497 eq29264
  have eq29309 : ∀ X0 X1 : G, (k X1 (σ x)) = X1 ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29274 X0 X1
       have j1 := eq13 X1 (σ x)
       grind)
    | (have r₁ := eq29274 X0 X1
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq29274 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29274
  have eq29338 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq50
       have i₂ := eq29309 (k sF2 sF2) x
       grind)
    | exact superpose eq29309 eq50
    | (have j1 := eq29309 X0 x
       grind)
    | exact resolve eq50 eq29309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq29309
  have eq29454 : ∀ X0 : G, x = (k x x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq29 eq29338
    | (have j0 := eq29338 x
       grind)
    | exact resolve eq29338 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq29338
  have eq29491 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq29454 X0
       have j1 := eq2054 x X0
       grind)
    | (have r₁ := eq29454 X0
       have r₂ := eq2054 x x
       grind)
    | (have r₁ := eq29454 x
       have r₂ := eq2054 x x
       grind)
    | exact resolve eq29454 eq2054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2054 eq29454
  have eq29868 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq698 x
       have i₂ := eq29491 x
       grind)
    | exact superpose eq29491 eq698
    | (have j0 := eq698 x
       grind)
    | exact resolve eq698 eq29491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq29874 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5129 x
       have i₂ := eq29491 x
       grind)
    | exact superpose eq29491 eq5129
    | (have j0 := eq5129 x
       grind)
    | (have r₁ := eq5129 x
       have r₂ := eq29491 x
       grind)
    | exact resolve eq5129 eq29491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5129 eq29491
  have eq29897 : x = (M.op x x) := by grind
  clear eq29874
  have eq29902 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq29868
  have eq29927 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq29902
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq29902
    | exact resolve eq29902 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq29902
  have eq29998 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq456 x X0
       have i₂ := eq29897
       grind)
    | exact superpose eq29897 eq456
    | exact resolve eq456 eq29897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29897
  have eq30621 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq29927 eq456
    | exact resolve eq456 eq29927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456 eq29927
  have eq31275 : y = (M.op x y) := by
    first
    | (have i₁ := eq29998 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29998
    | (have j0 := eq29998 y
       grind)
    | exact resolve eq29998 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq29998
  have eq31413 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq31275 eq21
    | exact resolve eq21 eq31275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq31275
  have eq31582 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq31413
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq31413
    | exact resolve eq31413 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq31413
  have eq33516 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30621 eq27
    | (have j1 := eq30621 (σ y)
       grind)
    | exact resolve eq27 eq30621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq30621
  have eq33646 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31582 eq33516
    | exact resolve eq33516 eq31582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31582 eq33516
  have eq33655 : False := by grind
  exact eq33655

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_x_pyy_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       have i₂ := eq14 (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq74 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq107 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq107 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq107
    | (have j0 := eq107 (σ X0)
       grind)
    | exact resolve eq107 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq62 (M.op X0 X0) x x X3
       have i₂ := eq61 X0 x x (M.op X0 X0)
       grind)
    | exact superpose eq61 eq62
    | exact resolve eq62 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq62
  have eq572 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq543 X0 (M.op X0 X0)
       grind)
    | exact superpose eq543 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq543 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq572 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq727 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq323 X0 (M.op X1 X1)
       have i₂ := eq583 X1 (σ X0)
       grind)
    | exact superpose eq583 eq323
    | exact resolve eq323 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323 eq583
  have eq756 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq727 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq727
    | exact resolve eq727 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq806 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq74 X1 X0
       grind)
    | (have i₁ := eq12 (σ X1) (σ X1)
       have i₂ := eq74 X0 X1
       grind)
    | exact superpose eq74 eq12
    | (have j0 := eq12 (σ X0) (σ X0)
       have j1 := eq74 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq74 X0 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq74 X0 X1
       grind)
    | exact resolve eq12 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq820 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq74 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq823 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq806 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq824 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq823 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq828 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq824 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq824
    | (have j0 := eq824 X0 X1
       grind)
    | exact resolve eq824 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq6272 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq358 X0
       grind)
    | exact superpose eq358 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq358 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq358 X0
       grind)
    | exact resolve eq13 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq6302 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq6272 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq6272 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq6272 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6272
  have eq11168 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq828 X0 X1
       have j1 := eq820 X0 X1
       grind)
    | (have r₁ := eq828 X0 X1
       have r₂ := eq820 X0 X1
       grind)
    | (have r₁ := eq828 X1 X1
       have r₂ := eq820 X1 X1
       grind)
    | exact resolve eq828 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820 eq828
  have eq11542 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11168 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq11168
    | exact resolve eq11168 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11623 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq11168 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11168
    | (have j0 := eq11168 x X0
       grind)
    | exact resolve eq11168 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11168
  have eq11771 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11542 X0 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq11542
    | (have j0 := eq11542 X0 X1
       grind)
    | exact resolve eq11542 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq11542
  have eq26443 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11623 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11623
    | (have j0 := eq11623 y
       grind)
    | exact resolve eq11623 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11623
  have eq26462 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26443
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq26443
    | exact resolve eq26443 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26443
  have eq26481 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq26462
    | exact resolve eq26462 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26462
  have eq27076 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11771 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq11771
    | (have j0 := eq11771 X1 X1
       grind)
    | exact resolve eq11771 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11771
  have eq27966 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq27076 y x
       grind)
    | exact superpose eq27076 eq71
    | (have j1 := eq27076 x x
       grind)
    | exact resolve eq71 eq27076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq27076
  have eq28313 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq27966
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq27966
    | exact resolve eq27966 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27966
  have eq28344 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq28313
    | exact resolve eq28313 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28313
  have eq28361 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28344 eq26481
    | exact resolve eq26481 eq28344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26481 eq28344
  have eq28368 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq28361
       have r₂ := eq27
       grind)
    | exact resolve eq28361 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28361
  have eq28399 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq28368 eq756
    | exact resolve eq756 eq28368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756 eq28368
  have eq28439 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq28 eq28399
    | exact resolve eq28399 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq28399
  have eq28443 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq28439 X0
       have j1 := eq13 X0 x
       grind)
    | (have r₁ := eq28439 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq28439 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28439
  have eq28501 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq107 x
       have i₂ := eq28443 x
       grind)
    | exact superpose eq28443 eq107
    | (have j0 := eq107 x
       grind)
    | exact resolve eq107 eq28443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28502 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq6302 x X0
       have i₂ := eq28443 x
       grind)
    | exact superpose eq28443 eq6302
    | (have j0 := eq6302 x X0
       grind)
    | exact resolve eq6302 eq28443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6302 eq28443
  have eq28533 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq28502 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28502
  have eq28534 : x = (M.op x x) := by grind
  clear eq28501
  have eq28556 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq28533 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28533
    | (have j0 := eq28533 X0
       grind)
    | exact resolve eq28533 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq28533
  have eq28992 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq543 x X0
       have i₂ := eq28534
       grind)
    | exact superpose eq28534 eq543
    | exact resolve eq543 eq28534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28534
  have eq29109 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq28556 eq107
    | (have j0 := eq107 (σ x)
       grind)
    | exact resolve eq107 eq28556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq28556
  have eq29142 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq29109
  have eq29833 : y = (M.op x y) := by
    first
    | (have i₁ := eq28992 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28992
    | (have j0 := eq28992 y
       grind)
    | exact resolve eq28992 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq28992
  have eq29962 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq29833 eq20
    | exact resolve eq20 eq29833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq29833
  have eq30131 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq29962
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29962
    | exact resolve eq29962 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq29962
  have eq32392 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq29142 eq543
    | exact resolve eq543 eq29142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543 eq29142
  have eq32449 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32392 eq26
    | (have j1 := eq32392 (σ y)
       grind)
    | exact resolve eq26 eq32392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq32392
  have eq32575 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30131 eq32449
    | exact resolve eq32449 eq30131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30131 eq32449
  have eq32584 : False := by grind
  exact eq32584

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pxx_pxy_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  have eq90 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq44 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq44
    | exact resolve eq44 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq174 : ∀ X0 : G, (M.op (M.op (M.op y (M.op x y)) x) X0) = X0 := by
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
  have eq175 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op y (M.op x y)) x)) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (M.op y (M.op x y)) x)) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, (M.op (M.op y (M.op x y)) x) ≠ (M.op (M.op y (M.op x y)) x) ∨ (M.op X0 X0) = (k X0 (M.op (M.op y (M.op x y)) x)) := by
    intro X0
    first
    | exact superpose eq174 eq13
    | (have j0 := eq13 X0 (M.op (M.op y (M.op x y)) x)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op y (M.op x y)) x)
       have r₂ := eq174 (M.op (M.op y (M.op x y)) x)
       grind)
    | exact resolve eq13 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op y (M.op x y)) x)) := by
    intro X0
    first
    | (have j0 := eq182 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq644 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq180 eq181
    | exact resolve eq181 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq181
  have eq694 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq644 X0 (M.op X0 X0)
       grind)
    | exact superpose eq644 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq644 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq694 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq733 : ∀ X0 X1 X2 : G, (M.op (k X0 (M.op X1 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq644 X0 X2
       have i₂ := eq695 X1 X0
       grind)
    | exact superpose eq695 eq644
    | exact resolve eq644 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742 : ∀ X0 : G, (σ (M.op x x)) = (k (σ x) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq35 (M.op X0 X0)
       have i₂ := eq695 X0 x
       grind)
    | exact superpose eq695 eq35
    | exact resolve eq35 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq746 : ∀ X0 : G, (τ (M.op (σ x) (σ x))) = (k x (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq90 (M.op X0 X0)
       have i₂ := eq695 X0 sF2
       grind)
    | exact superpose eq695 eq90
    | exact resolve eq90 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq695
  have eq1159 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq1160 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1216 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1217 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1216 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216
  have eq1529 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1159
       grind)
    | exact superpose eq1159 eq39
    | exact resolve eq39 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq1159
  have eq1530 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1529
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1529
    | exact resolve eq1529 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529
  have eq1532 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq1530
    | exact resolve eq1530 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1530
  have eq1756 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1532 eq1160
    | exact resolve eq1160 eq1532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160 eq1532
  have eq1763 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1756
       have r₂ := eq27
       grind)
    | exact resolve eq1756 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1756
  have eq1786 : (τ (σ x)) = (k x (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1763 eq746
    | exact resolve eq746 eq1763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1763
  have eq1792 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq1786
    | exact resolve eq1786 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1786
  have eq1799 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq1217 x
       grind)
    | (have r₁ := eq1792
       have r₂ := eq1217 x
       grind)
    | exact resolve eq1792 eq1217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1792
  have eq1808 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq644 x X0
       have i₂ := eq1799
       grind)
    | exact superpose eq1799 eq644
    | exact resolve eq644 eq1799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1799
  have eq1839 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1808 y
       grind)
    | exact superpose eq1808 eq18
    | (have j1 := eq1808 y
       grind)
    | exact resolve eq18 eq1808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1808
  have eq1869 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1839
  have eq1884 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ y)) (σ x)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1869 eq175
    | exact resolve eq175 eq1869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq1869
  have eq1893 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1884 X0
       have i₂ := eq644 sF3 sF2
       grind)
    | exact superpose eq644 eq1884
    | exact resolve eq1884 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1884
  have eq1922 : (τ (σ x)) = (k x (τ (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1893 eq746
    | exact resolve eq746 eq1893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746 eq1893
  have eq1928 : x = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq1922
    | exact resolve eq1922 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1922
  have eq1952 : x ≠ x ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1217 x
       have i₂ := eq1928
       grind)
    | exact superpose eq1928 eq1217
    | (have j0 := eq1217 x
       grind)
    | (have r₁ := eq1217 x
       have r₂ := eq1928
       grind)
    | exact resolve eq1217 eq1928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1928
  have eq1953 : x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq1952
  have eq1964 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq644 x X0
       have i₂ := eq1953
       grind)
    | exact superpose eq1953 eq644
    | exact resolve eq644 eq1953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1953
  have eq2029 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1964 y
       grind)
    | exact superpose eq1964 eq18
    | (have j1 := eq1964 y
       grind)
    | exact resolve eq18 eq1964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1964
  have eq2059 : y = (M.op x y) := by grind
  clear eq2029
  have eq2085 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2059
       grind)
    | exact superpose eq2059 eq24
    | exact resolve eq24 eq2059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2088 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) (M.op x y)) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq174 X0
       have i₂ := eq2059
       grind)
    | exact superpose eq2059 eq174
    | exact resolve eq174 eq2059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq2091 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op (M.op x y) (M.op x y)) x)) := by
    intro X0
    first
    | (have i₁ := eq183 X0
       have i₂ := eq2059
       grind)
    | exact superpose eq2059 eq183
    | exact resolve eq183 eq2059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq2059
  have eq2094 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq2091 X0
       have i₂ := eq644 sF0 x
       grind)
    | exact superpose eq644 eq2091
    | exact resolve eq2091 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2091
  have eq2097 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2088 X0
       have i₂ := eq644 sF0 x
       grind)
    | exact superpose eq644 eq2088
    | exact resolve eq2088 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644 eq2088
  have eq2105 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2085 eq20
    | exact resolve eq20 eq2085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2085
  have eq2197 : ∀ X0 X1 : G, (M.op (k X0 x) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq733 X0 x X1
       have i₂ := eq2097 x
       grind)
    | exact superpose eq2097 eq733
    | exact resolve eq733 eq2097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq2200 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq742 x
       have i₂ := eq2097 x
       grind)
    | exact superpose eq2097 eq742
    | exact resolve eq742 eq2097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq2097
  have eq2214 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2200
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2200
    | exact resolve eq2200 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2200
  have eq2746 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2214 eq1217
    | (have j0 := eq1217 (σ x)
       grind)
    | (have r₁ := eq1217 (σ x)
       have r₂ := eq2214
       grind)
    | exact resolve eq1217 eq2214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217 eq2214
  have eq2747 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2746
  have eq2749 : (σ x) = (k (σ x) x) := by
    first
    | (have i₁ := eq2747
       have i₂ := eq2094 sF2
       grind)
    | exact superpose eq2094 eq2747
    | exact resolve eq2747 eq2094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2094 eq2747
  have eq2948 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq2749 eq2197
    | exact resolve eq2197 eq2749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2197 eq2749
  have eq3068 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2948 eq26
    | (have j1 := eq2948 (σ y)
       grind)
    | exact resolve eq26 eq2948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2948
  have eq3142 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq3068 eq27
    | exact resolve eq27 eq3068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq3068
  have eq3153 : False := by grind
  exact eq3153

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_pxy_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       have i₂ := eq9 (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X1 X2
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
  clear eq18
  have eq33 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X1) ≠ (M.op (M.op X0 (M.op X1 X0)) X1) ∨ (M.op (M.op (M.op X0 (M.op X1 X0)) X1) X2) = (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op (M.op X0 (M.op X1 X0)) X1)
       have i₂ := eq9 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X2 (M.op (M.op X0 (M.op X1 X0)) X1)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have r₂ := eq9 (M.op (M.op X1 (M.op X2 X1)) X2) X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X0)) X1) X2) = (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq33 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq35 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 X1 X2
       have i₂ := eq9 X2 X0 X1
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq58 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq58
    | (have j0 := eq58 (σ X0) (σ X1)
       grind)
    | exact resolve eq58 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq35 X1 X2 (σ X0)
       grind)
    | exact superpose eq35 eq30
    | exact resolve eq30 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq81 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq35 X1 X2 (τ X0)
       grind)
    | exact superpose eq35 eq17
    | exact resolve eq17 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq35
  have eq85 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81
    | exact resolve eq81 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq86 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq80
    | exact resolve eq80 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq95 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X1 (M.op X2 X1)) X2)) X0) = X0 ∨ (M.op (σ (M.op (M.op X1 (M.op X2 X1)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))
       have i₂ := eq85 X0 X1 X2
       grind)
    | exact superpose eq85 eq58
    | (have j0 := eq58 X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))
       grind)
    | exact resolve eq58 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq96 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X1 (M.op X2 X1)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq95 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq135 : ∀ X0 X1 X2 : G, (M.op (τ (M.op (M.op X1 (M.op X2 X1)) X2)) X0) = X0 ∨ (M.op (τ (M.op (M.op X1 (M.op X2 X1)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))
       have i₂ := eq86 X0 X1 X2
       grind)
    | exact superpose eq86 eq58
    | (have j0 := eq58 X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))
       grind)
    | exact resolve eq58 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq136 : ∀ X0 X1 X2 : G, (M.op (τ (M.op (M.op X1 (M.op X2 X1)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq135 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq153 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq24 (M.op X0 X0) x x X3
       have i₂ := eq23 X0 x x (M.op X0 X0)
       grind)
    | exact superpose eq23 eq24
    | exact resolve eq24 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq24
  have eq212 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq69 y x
       grind)
    | exact superpose eq69 eq16
    | (have j1 := eq69 y x
       grind)
    | exact resolve eq16 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq271 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X0 X0) (M.op X1 X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq96 X2 X0 (M.op X1 X1)
       have i₂ := eq153 X1 X0
       grind)
    | exact superpose eq153 eq96
    | exact resolve eq96 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq290 : ∀ X1 X2 : G, (M.op (σ (M.op X1 X1)) X2) = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq271 x X1 X2
       have i₂ := eq153 x (M.op X1 X1)
       grind)
    | (have i₁ := eq271 x X1 X2
       have i₂ := eq153 x (M.op (M.op x x) (M.op X1 X1))
       grind)
    | exact superpose eq153 eq271
    | exact resolve eq271 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq554 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq212
       have i₂ := eq58 y x
       grind)
    | exact superpose eq58 eq212
    | (have j1 := eq58 (σ y) (σ x)
       grind)
    | exact resolve eq212 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq212
  have eq555 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq554
  have eq3005 : ∀ X0 : G, (M.op (M.op (M.op y y) x) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq555
       grind)
    | exact superpose eq555 eq9
    | exact resolve eq9 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq3030 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3005 X0
       have i₂ := eq153 y x
       grind)
    | (have i₁ := eq3005 X0
       have i₂ := eq153 X0 (M.op (M.op y y) x)
       grind)
    | exact superpose eq153 eq3005
    | exact resolve eq3005 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3005
  have eq26049 : ∀ X0 X1 : G, (M.op (τ (M.op (M.op (σ y) (σ y)) (σ x))) X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq136 X0 (σ y) (σ x)
       have i₂ := eq3030 X1
       grind)
    | exact superpose eq3030 eq136
    | (have j1 := eq3030 X1
       grind)
    | exact resolve eq136 eq3030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq3030
  have eq26073 : ∀ X0 X1 : G, (M.op (τ (σ x)) X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26049 X0 X1
       have i₂ := eq153 (σ y) (σ x)
       grind)
    | (have i₁ := eq26049 X0 X1
       have i₂ := eq153 X0 (M.op (M.op (σ y) (σ y)) (σ x))
       grind)
    | exact superpose eq153 eq26049
    | (have j0 := eq26049 X0 X1
       grind)
    | exact resolve eq26049 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq26049
  have eq26087 : ∀ X0 X1 : G, (M.op x X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26073 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq26073
    | (have j0 := eq26073 X0 X0
       grind)
    | exact resolve eq26073 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26073
  have eq26586 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq26087 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26087
  have eq26587 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq26586 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26586
  have eq26666 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq290 x X0
       have i₂ := eq26587 x
       grind)
    | exact superpose eq26587 eq290
    | exact resolve eq290 eq26587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq26958 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26666 (σ y)
       grind)
    | exact superpose eq26666 eq16
    | exact resolve eq16 eq26666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26666
  have eq27175 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq26958
       have i₂ := eq26587 y
       grind)
    | exact superpose eq26587 eq26958
    | exact resolve eq26958 eq26587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26587 eq26958
  have eq27176 : False := by grind
  exact eq27176

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_pyy_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       have i₂ := eq9 (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X1 X2
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
  clear eq18
  have eq33 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X1) ≠ (M.op (M.op X0 (M.op X1 X0)) X1) ∨ (M.op (M.op (M.op X0 (M.op X1 X0)) X1) X2) = (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op (M.op X0 (M.op X1 X0)) X1)
       have i₂ := eq9 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X2 (M.op (M.op X0 (M.op X1 X0)) X1)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have r₂ := eq9 (M.op (M.op X1 (M.op X2 X1)) X2) X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X0)) X1) X2) = (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq33 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq35 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 X1 X2
       have i₂ := eq9 X2 X0 X1
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq58 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq58
    | (have j0 := eq58 (σ X0) (σ X1)
       grind)
    | exact resolve eq58 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq35 X1 X2 (σ X0)
       grind)
    | exact superpose eq35 eq30
    | exact resolve eq30 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq81 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq35 X1 X2 (τ X0)
       grind)
    | exact superpose eq35 eq17
    | exact resolve eq17 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq35
  have eq85 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81
    | exact resolve eq81 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq86 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq80
    | exact resolve eq80 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq95 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X1 (M.op X2 X1)) X2)) X0) = X0 ∨ (M.op (σ (M.op (M.op X1 (M.op X2 X1)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))
       have i₂ := eq85 X0 X1 X2
       grind)
    | exact superpose eq85 eq58
    | (have j0 := eq58 X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))
       grind)
    | exact resolve eq58 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq96 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X1 (M.op X2 X1)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq95 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq135 : ∀ X0 X1 X2 : G, (M.op (τ (M.op (M.op X1 (M.op X2 X1)) X2)) X0) = X0 ∨ (M.op (τ (M.op (M.op X1 (M.op X2 X1)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))
       have i₂ := eq86 X0 X1 X2
       grind)
    | exact superpose eq86 eq58
    | (have j0 := eq58 X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))
       grind)
    | exact resolve eq58 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq136 : ∀ X0 X1 X2 : G, (M.op (τ (M.op (M.op X1 (M.op X2 X1)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq135 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq153 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq24 (M.op X0 X0) x x X3
       have i₂ := eq23 X0 x x (M.op X0 X0)
       grind)
    | exact superpose eq23 eq24
    | exact resolve eq24 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq24
  have eq212 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq69 y x
       grind)
    | exact superpose eq69 eq16
    | (have j1 := eq69 y x
       grind)
    | exact resolve eq16 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq271 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X0 X0) (M.op X1 X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq96 X2 X0 (M.op X1 X1)
       have i₂ := eq153 X1 X0
       grind)
    | exact superpose eq153 eq96
    | exact resolve eq96 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq290 : ∀ X1 X2 : G, (M.op (σ (M.op X1 X1)) X2) = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq271 x X1 X2
       have i₂ := eq153 x (M.op X1 X1)
       grind)
    | (have i₁ := eq271 x X1 X2
       have i₂ := eq153 x (M.op (M.op x x) (M.op X1 X1))
       grind)
    | exact superpose eq153 eq271
    | exact resolve eq271 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq554 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq212
       have i₂ := eq58 y x
       grind)
    | exact superpose eq58 eq212
    | (have j1 := eq58 (σ y) (σ x)
       grind)
    | exact resolve eq212 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq212
  have eq555 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq554
  have eq3008 : ∀ X0 : G, (M.op (M.op (M.op y y) x) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq555
       grind)
    | exact superpose eq555 eq9
    | exact resolve eq9 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq3033 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3008 X0
       have i₂ := eq153 y x
       grind)
    | (have i₁ := eq3008 X0
       have i₂ := eq153 X0 (M.op (M.op y y) x)
       grind)
    | exact superpose eq153 eq3008
    | exact resolve eq3008 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3008
  have eq26041 : ∀ X0 X1 : G, (M.op (τ (M.op (M.op (σ y) (σ y)) (σ x))) X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq136 X0 (σ y) (σ x)
       have i₂ := eq3033 X1
       grind)
    | exact superpose eq3033 eq136
    | (have j1 := eq3033 X1
       grind)
    | exact resolve eq136 eq3033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq3033
  have eq26065 : ∀ X0 X1 : G, (M.op (τ (σ x)) X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26041 X0 X1
       have i₂ := eq153 (σ y) (σ x)
       grind)
    | (have i₁ := eq26041 X0 X1
       have i₂ := eq153 X0 (M.op (M.op (σ y) (σ y)) (σ x))
       grind)
    | exact superpose eq153 eq26041
    | (have j0 := eq26041 X0 X1
       grind)
    | exact resolve eq26041 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq26041
  have eq26079 : ∀ X0 X1 : G, (M.op x X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26065 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq26065
    | (have j0 := eq26065 X0 X0
       grind)
    | exact resolve eq26065 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26065
  have eq26578 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq26079 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26079
  have eq26579 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq26578 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26578
  have eq26658 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq290 x X0
       have i₂ := eq26579 x
       grind)
    | exact superpose eq26579 eq290
    | exact resolve eq290 eq26579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq26950 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26658 (σ y)
       grind)
    | exact superpose eq26658 eq16
    | exact resolve eq16 eq26658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26658
  have eq27167 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq26950
       have i₂ := eq26579 y
       grind)
    | exact superpose eq26579 eq26950
    | exact resolve eq26950 eq26579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26579 eq26950
  have eq27168 : False := by grind
  exact eq27168

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_x_pxx_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq174 : ∀ X0 : G, (M.op (M.op (M.op y (M.op x y)) x) X0) = X0 := by
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
  have eq175 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X1) ≠ (M.op (M.op X0 (M.op X1 X0)) X1) ∨ (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X0 (M.op X1 X0)) X1)
       have i₂ := eq16 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 X2 (M.op (M.op X0 (M.op X1 X0)) X1)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have r₂ := eq16 (M.op (M.op X1 (M.op X2 X1)) X2) X1 X2
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq178 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq180 : ∀ X0 : G, (M.op (M.op y (M.op x y)) x) ≠ (M.op (M.op y (M.op x y)) x) ∨ (k X0 (M.op (M.op y (M.op x y)) x)) = X0 := by
    intro X0
    first
    | exact superpose eq174 eq13
    | (have j0 := eq13 X0 (M.op (M.op y (M.op x y)) x)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op y (M.op x y)) x)
       have r₂ := eq174 (M.op (M.op y (M.op x y)) x)
       grind)
    | exact resolve eq13 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op y (M.op x y)) x)) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (M.op y (M.op x y)) x)) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq183 : ∀ X0 : G, (k X0 (M.op (M.op y (M.op x y)) x)) = X0 := by
    intro X0
    first
    | (have j0 := eq180 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq184 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) ≠ (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) ∨ (k X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq175 eq13
    | (have j0 := eq13 X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))
       have r₂ := eq175 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))
       grind)
    | exact resolve eq13 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq187 : ∀ X0 : G, (k X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))) = X0 := by
    intro X0
    first
    | (have j0 := eq184 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq327 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op y (M.op x y)) x))) := by
    intro X0
    first
    | exact superpose eq183 eq34
    | exact resolve eq34 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq183
  have eq357 : ∀ X0 : G, (k X0 (σ (M.op (M.op y (M.op x y)) x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq327 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq327
    | exact resolve eq327 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq396 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq723 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq724 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq769 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq770 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq769 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq853 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq396 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq179 X1 X2 (σ X0)
       grind)
    | exact superpose eq179 eq396
    | exact resolve eq396 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq396
  have eq870 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq853 X0 X1 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq853
    | exact resolve eq853 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq1255 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq723
       grind)
    | exact superpose eq723 eq39
    | exact resolve eq39 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq1256 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1255
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1255
    | exact resolve eq1255 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255
  have eq1258 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq1256
    | exact resolve eq1256 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256
  have eq1548 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq181 eq182
    | exact resolve eq182 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq182
  have eq1607 : ∀ X0 X1 X2 : G, (k X1 (τ (M.op (M.op X0 X0) (M.op X2 X2)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq870 X1 X0 (M.op X2 X2)
       have i₂ := eq1548 X2 X0
       grind)
    | exact superpose eq1548 eq870
    | exact resolve eq870 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq1623 : ∀ X1 X2 : G, (k X1 (τ (M.op X2 X2))) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq1607 x X1 X2
       have i₂ := eq1548 x (M.op X2 X2)
       grind)
    | exact superpose eq1548 eq1607
    | exact resolve eq1607 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1607
  have eq4120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1258 eq724
    | exact resolve eq724 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq4129 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq4120
       have r₂ := eq27
       grind)
    | exact resolve eq4120 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4120
  have eq4146 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq4129 eq1623
    | exact resolve eq1623 eq4129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1623 eq4129
  have eq4222 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq29 eq4146
    | exact resolve eq4146 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4146
  have eq4233 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq4222 X0
       have j1 := eq13 X0 x
       grind)
    | (have r₁ := eq4222 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq4222 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4222
  have eq4249 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq723
       have i₂ := eq4233 y
       grind)
    | exact superpose eq4233 eq723
    | exact resolve eq723 eq4233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723 eq4233
  have eq4255 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4249
  have eq4280 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1548 x X0
       have i₂ := eq4255
       grind)
    | exact superpose eq4255 eq1548
    | exact resolve eq1548 eq4255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4255
  have eq4437 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4280 y
       grind)
    | exact superpose eq4280 eq18
    | (have j1 := eq4280 y
       grind)
    | exact resolve eq18 eq4280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4280
  have eq4520 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4437
  have eq4566 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4520 eq27
    | exact resolve eq27 eq4520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4570 : ∀ X0 : G, (k X0 (M.op (M.op (σ y) (σ y)) (σ x))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4520 eq187
    | exact resolve eq187 eq4520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq4520
  have eq4625 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4570 X0
       have i₂ := eq1548 sF3 sF2
       grind)
    | exact superpose eq1548 eq4570
    | exact resolve eq4570 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4570
  have eq4662 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4625 eq1258
    | exact resolve eq1258 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258 eq4625
  have eq4667 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq4662
  have eq4676 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq4667
       have r₂ := eq4566
       grind)
    | exact resolve eq4667 eq4566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4566 eq4667
  have eq4870 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1548 x X0
       have i₂ := eq4676
       grind)
    | exact superpose eq4676 eq1548
    | exact resolve eq1548 eq4676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4676
  have eq4969 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4870 y
       grind)
    | exact superpose eq4870 eq18
    | (have j1 := eq4870 y
       grind)
    | exact resolve eq18 eq4870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4870
  have eq5052 : y = (M.op x y) := by grind
  clear eq4969
  have eq5099 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq5052
       grind)
    | exact superpose eq5052 eq24
    | exact resolve eq24 eq5052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq5113 : ∀ X0 : G, (k X0 (σ (M.op (M.op (M.op x y) (M.op x y)) x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq357 X0
       have i₂ := eq5052
       grind)
    | exact superpose eq5052 eq357
    | exact resolve eq357 eq5052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq5052
  have eq5161 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq5113 X0
       have i₂ := eq1548 sF0 x
       grind)
    | exact superpose eq1548 eq5113
    | exact resolve eq5113 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5113
  have eq5181 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq5161 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5161
    | (have j0 := eq5161 X0
       grind)
    | exact resolve eq5161 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5161
  have eq5187 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5099 eq20
    | exact resolve eq20 eq5099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5099
  have eq5980 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5181 eq770
    | (have j0 := eq770 (σ x)
       grind)
    | (have r₁ := eq770 (σ x)
       have r₂ := eq5181 (σ x)
       grind)
    | exact resolve eq770 eq5181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770 eq5181
  have eq6000 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5980
  have eq6026 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq6000 eq1548
    | exact resolve eq1548 eq6000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548 eq6000
  have eq6121 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6026 eq26
    | (have j1 := eq6026 (σ y)
       grind)
    | exact resolve eq26 eq6026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq6026
  have eq6426 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq6121 eq27
    | exact resolve eq27 eq6121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq6121
  have eq6489 : False := by grind
  exact eq6489
