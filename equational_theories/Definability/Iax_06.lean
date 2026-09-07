import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation647`: `x = x ◇ (y ◇ ((y ◇ z) ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pyy_pxy_Equation647 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law647 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law647.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) = X0 := by
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
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X0 (M.op X1 (M.op (M.op X1 X2) X2))
       have i₂ := eq8 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq22 X0 x x X3
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq22
    | exact resolve eq22 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X0 X0)
       have i₂ := eq23 X0 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq11
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq23 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq37 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (M.op X0 X0)
       have i₂ := eq33 X0 (τ X1)
       grind)
    | exact superpose eq33 eq15
    | exact resolve eq15 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
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
  have eq44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq45 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
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
  clear eq15
  have eq47 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq55 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq68 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq47 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq47 eq13
    | (have j1 := eq47 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq139 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq44 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq380 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq424 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq380 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq380
    | (have j0 := eq380 X0 X1
       grind)
    | exact resolve eq380 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq1035 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq37 X1 X1
       have i₂ := eq424 X0 X1
       grind)
    | exact superpose eq424 eq37
    | (have j1 := eq424 X2 X0
       grind)
    | exact resolve eq37 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq424
  have eq1070 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq139 (M.op X0 X0)
       have i₂ := eq33 X0 (M.op X0 X0)
       grind)
    | exact superpose eq33 eq139
    | (have j0 := eq139 (M.op X0 X0)
       grind)
    | exact resolve eq139 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq1084 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq139 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq139
    | (have j0 := eq139 (τ X0)
       grind)
    | exact resolve eq139 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq139
  have eq1096 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1070 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070
  have eq1100 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1084 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1084
    | (have j0 := eq1084 X0
       grind)
    | exact resolve eq1084 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1109 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1100 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1100
    | (have j0 := eq1100 X0
       grind)
    | exact resolve eq1100 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100
  have eq1577 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ (M.op X0 X0)) X1
       have i₂ := eq1096 X0
       grind)
    | exact superpose eq1096 eq23
    | exact resolve eq23 eq1096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1096
  have eq1639 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq68 x y X0
       grind)
    | exact superpose eq68 eq14
    | (have j1 := eq68 X0 y X0
       grind)
    | exact resolve eq14 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq1694 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq1639 X0
       have j1 := eq1035 y X0 x
       grind)
    | (have r₁ := eq1639 X0
       have r₂ := eq1035 y x x
       grind)
    | exact resolve eq1639 eq1035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035 eq1639
  have eq1730 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq55 X0 (σ y)
       have i₂ := eq1694 (σ X0)
       grind)
    | exact superpose eq1694 eq55
    | exact resolve eq55 eq1694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq1694
  have eq1736 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq1730 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1730
    | exact resolve eq1730 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1730
  have eq1856 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1109 y
       have i₂ := eq1736 y
       grind)
    | exact superpose eq1736 eq1109
    | (have j0 := eq1109 y
       grind)
    | (have r₁ := eq1109 y
       have r₂ := eq1736 y
       grind)
    | exact resolve eq1109 eq1736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109 eq1736
  have eq1871 : y = (M.op y y) := by grind
  clear eq1856
  have eq1954 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 y X0
       have i₂ := eq1871
       grind)
    | exact superpose eq1871 eq23
    | exact resolve eq23 eq1871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq2689 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1577 y X0
       have i₂ := eq1871
       grind)
    | exact superpose eq1871 eq1577
    | exact resolve eq1577 eq1871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1577 eq1871
  have eq2998 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2689 (σ x)
       grind)
    | exact superpose eq2689 eq14
    | exact resolve eq14 eq2689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2689
  have eq3002 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2998
       have i₂ := eq1954 x
       grind)
    | exact superpose eq1954 eq2998
    | exact resolve eq2998 eq1954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1954 eq2998
  have eq3003 : False := by grind
  exact eq3003

/-- `Equation653`: `x = x ◇ (y ◇ ((z ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pyx_pxx_pyx_Equation653 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law653 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law653.models_iff G M).mp hM
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
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq91 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq95 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq91 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq91 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq91 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq111 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq95 (σ X1) (σ X0)
       grind)
    | exact superpose eq95 eq13
    | exact resolve eq13 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq111 X0 X1
       have i₂ := eq95 X1 X0
       grind)
    | exact superpose eq95 eq111
    | exact resolve eq111 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq111
  have eq1278 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq118 x y
       grind)
    | exact superpose eq118 eq14
    | (have r₁ := eq14
       have r₂ := eq118 x y
       grind)
    | exact resolve eq14 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq1302 : False := by grind
  exact eq1302

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

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation695 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law695 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law695.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
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
  have eq19 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
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
  have eq32 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq16 eq12
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
  clear eq17
  have eq44 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X2 (M.op X0 X0) (M.op X1 X1)
       have i₂ := eq19 X1 X0 (M.op X0 X0)
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (M.op X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X1 X1) (M.op X0 X0)
       have i₂ := eq19 X1 X0 (M.op X0 X0)
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X1 X1) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (M.op X2 X2) (M.op (M.op X1 X1) X0)) (M.op (M.op X1 X1) X0) X2
       have i₂ := eq19 (M.op (M.op X2 X2) (M.op (M.op X1 X1) X0)) X1 X0
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 x X1 (M.op X1 X1)
       have i₂ := eq44 (M.op X1 X1) X0 x
       grind)
    | (have i₁ := eq19 (M.op X1 X1) X1 (M.op X1 X1)
       have i₂ := eq44 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq44 eq19
    | exact resolve eq19 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    grind
  clear eq44
  have eq286 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq300 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq378 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq386 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (M.op X2 X2) X1) X1 X2
       have i₂ := eq235 (M.op (M.op X2 X2) X1) X0
       grind)
    | (have i₁ := eq8 (M.op (M.op X2 X2) X1) X1 X2
       have i₂ := eq235 X0 (M.op (M.op X2 X2) X1)
       grind)
    | exact superpose eq235 eq8
    | exact resolve eq8 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq235 (σ X0) X1
       grind)
    | (have i₁ := eq31 X0 X0
       have i₂ := eq235 X0 (σ X0)
       grind)
    | exact superpose eq235 eq31
    | exact resolve eq31 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq235
  have eq471 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1 (M.op X0 X0)
       have i₂ := eq378 X0 (σ X1)
       grind)
    | exact superpose eq378 eq39
    | exact resolve eq39 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0)
       have i₂ := eq378 X0 (τ X1)
       grind)
    | exact superpose eq378 eq16
    | exact resolve eq16 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq553 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 X3)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq19 X3 x (M.op X0 (M.op X2 X2))
       have i₂ := eq51 X2 x X0
       grind)
    | exact superpose eq51 eq19
    | exact resolve eq19 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq51
  have eq2449 : ∀ X0 X1 : G, (τ (τ (M.op X0 X0))) = (k X1 (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1 (τ (M.op X0 X0))
       have i₂ := eq471 X0 (σ X1)
       grind)
    | exact superpose eq471 eq39
    | exact resolve eq39 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq471
  have eq2725 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (k X1 (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (σ (M.op X0 X0))
       have i₂ := eq472 X0 (τ X1)
       grind)
    | exact superpose eq472 eq16
    | exact resolve eq16 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3641 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
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
  have eq3793 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3641 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq3641
    | (have j0 := eq3641 X0 X1
       grind)
    | exact resolve eq3641 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3641
  have eq5945 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq392 X1 (σ (M.op X0 X0))
       have i₂ := eq472 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq472 eq392
    | (have j0 := eq392 X1 (σ (M.op X0 X0))
       grind)
    | exact resolve eq392 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq5946 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (σ (M.op X0 X0)))) ∨ (M.op X1 X1) = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq392 X1 (σ (σ (M.op X0 X0)))
       have i₂ := eq2725 X0 (σ (σ (M.op X0 X0)))
       grind)
    | exact superpose eq2725 eq392
    | (have j0 := eq392 X1 (σ (σ (M.op X0 X0)))
       grind)
    | exact resolve eq392 eq2725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725
  have eq5948 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) ∨ (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq392 X1 (τ (τ (M.op X0 X0)))
       have i₂ := eq2449 X0 (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq2449 eq392
    | (have j0 := eq392 X1 (τ (τ (M.op X0 X0)))
       grind)
    | exact resolve eq392 eq2449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2449
  have eq5949 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq392 X1 (M.op X0 X0)
       have i₂ := eq247 X0 X0
       grind)
    | exact superpose eq247 eq392
    | (have j0 := eq392 X1 (M.op X0 X0)
       grind)
    | exact resolve eq392 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq392
  have eq6107 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq5949 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5949
  have eq6108 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq5948 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5948
  have eq6110 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq5946 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5946
  have eq6111 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq5945 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5945
  have eq6147 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6108 X0 X1
       have i₂ := eq10 (τ (M.op X0 X0))
       grind)
    | exact superpose eq10 eq6108
    | exact resolve eq6108 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6108
  have eq6346 : ∀ X0 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq6107 X2 x
       have i₂ := eq6107 X0 x
       grind)
    | exact superpose eq6107 eq6107
    | exact resolve eq6107 eq6107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6727 : ∀ X0 X2 : G, (τ (M.op X0 X0)) = (τ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq6147 X2 x
       have i₂ := eq6147 X0 x
       grind)
    | exact superpose eq6147 eq6147
    | exact resolve eq6147 eq6147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6766 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6147 x X1
       have i₂ := eq6147 X0 x
       grind)
    | exact superpose eq6147 eq6147
    | exact resolve eq6147 eq6147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6854 : ∀ X0 X2 : G, (τ (M.op X0 X0)) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq6107 X2 x
       have i₂ := eq6147 X0 x
       grind)
    | exact superpose eq6147 eq6107
    | exact resolve eq6107 eq6147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6865 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (M.op X2 X2) X1) X1 X2
       have i₂ := eq6147 X0 (M.op (M.op X2 X2) X1)
       grind)
    | exact superpose eq6147 eq8
    | exact resolve eq8 eq6147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6900 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X1 X1) X1
       have i₂ := eq6147 X0 (M.op X1 X1)
       grind)
    | exact superpose eq6147 eq8
    | exact resolve eq8 eq6147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7355 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq286
       have i₂ := eq3793 y x
       grind)
    | exact superpose eq3793 eq286
    | (have j1 := eq3793 (σ y) (σ x)
       grind)
    | (have r₁ := eq286
       have r₂ := eq3793 y x
       grind)
    | exact resolve eq286 eq3793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286 eq3793
  have eq7356 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq7355
  have eq7427 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6346 X1 x
       have i₂ := eq6111 X0 x
       grind)
    | exact superpose eq6111 eq6346
    | exact resolve eq6346 eq6111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6346
  have eq8365 : ∀ X0 X2 : G, (τ (τ (M.op X0 X0))) = (τ (τ (M.op X2 X2))) := by
    intro X0 X2
    first
    | (have i₁ := eq6766 X2 x
       have i₂ := eq6766 X0 x
       grind)
    | exact superpose eq6766 eq6766
    | exact resolve eq6766 eq6766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8502 : ∀ X0 X2 : G, (τ (τ (M.op X0 X0))) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq6107 X2 x
       have i₂ := eq6766 X0 x
       grind)
    | exact superpose eq6766 eq6107
    | exact resolve eq6107 eq6766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8505 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6147 x X1
       have i₂ := eq6766 X0 x
       grind)
    | exact superpose eq6766 eq6147
    | exact resolve eq6147 eq6766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8510 : ∀ X0 X2 : G, (τ (M.op X2 X2)) = (τ (τ (τ (M.op X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq6727 x X2
       have i₂ := eq6766 X0 x
       grind)
    | exact superpose eq6766 eq6727
    | exact resolve eq6727 eq6766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6727 eq6766
  have eq8877 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6854 X1 x
       have i₂ := eq6111 X0 x
       grind)
    | exact superpose eq6111 eq6854
    | exact resolve eq6854 eq6111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6854
  have eq88511 : ∀ X0 : G, (M.op X0 X0) = (τ (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq6147 (σ x) X0
       have i₂ := eq7356
       grind)
    | exact superpose eq7356 eq6147
    | exact resolve eq6147 eq7356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7356
  have eq88682 : ∀ X0 : G, (M.op X0 X0) = y ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq88511 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq88511
    | exact resolve eq88511 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88511
  have eq90596 : y ≠ y ∨ y = (M.op x x) := by
    first
    | (have j0 := eq88682 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88682
  have eq90597 : y = (M.op x x) := by grind
  clear eq90596
  have eq91165 : ∀ X0 X1 : G, (M.op y (M.op (M.op X0 X0) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1 X0 x
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq53
    | exact resolve eq53 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq91201 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq386 x X1 X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq386
    | exact resolve eq386 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq91207 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq553 X0 X1 x
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq553
    | exact resolve eq553 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq91215 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq6107 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq6107
    | exact resolve eq6107 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6107
  have eq91216 : ∀ X0 : G, (M.op X0 X0) = (σ (σ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq6110 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq6110
    | exact resolve eq6110 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6110
  have eq91217 : ∀ X0 : G, (M.op X0 X0) = (σ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq6111 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq6111
    | exact resolve eq6111 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6111
  have eq91218 : ∀ X0 : G, (M.op X0 X0) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq6147 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq6147
    | exact resolve eq6147 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6147
  have eq91272 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X1 (τ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq6865 x X1 X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq6865
    | exact resolve eq6865 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6865
  have eq91297 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (σ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq7427 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq7427
    | exact resolve eq7427 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7427
  have eq91300 : ∀ X0 : G, (τ (τ (M.op X0 X0))) = (τ (τ y)) := by
    intro X0
    first
    | (have i₁ := eq8365 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq8365
    | exact resolve eq8365 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8365
  have eq91302 : ∀ X0 : G, (σ (M.op X0 X0)) = (τ (τ y)) := by
    intro X0
    first
    | (have i₁ := eq8502 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq8502
    | exact resolve eq8502 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8502
  have eq91304 : ∀ X0 : G, (M.op X0 X0) = (τ (τ (τ y))) := by
    intro X0
    first
    | (have i₁ := eq8505 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq8505
    | exact resolve eq8505 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8505
  have eq91305 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (τ (τ y))) := by
    intro X0
    first
    | (have i₁ := eq8510 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq8510
    | exact resolve eq8510 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8510
  have eq91308 : ∀ X0 : G, (τ (M.op X0 X0)) = (σ (σ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq8877 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq8877
    | exact resolve eq8877 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8877 eq90597
  have eq91332 : (σ (σ (σ y))) = (τ (τ (τ y))) := by
    first
    | (have i₁ := eq91305 x
       have i₂ := eq91308 x
       grind)
    | exact superpose eq91308 eq91305
    | exact resolve eq91305 eq91308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91305
  have eq91333 : (τ (τ y)) = (τ (σ (σ (σ y)))) := by
    first
    | (have i₁ := eq91300 x
       have i₂ := eq91308 x
       grind)
    | exact superpose eq91308 eq91300
    | exact resolve eq91300 eq91308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91300
  have eq91335 : (σ (σ (σ y))) = (τ (τ y)) := by
    first
    | (have i₁ := eq91297 x
       have i₂ := eq91302 x
       grind)
    | exact superpose eq91302 eq91297
    | exact resolve eq91297 eq91302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91297
  have eq91380 : (σ (σ y)) = (τ y) := by
    first
    | (have i₁ := eq91217 x
       have i₂ := eq91218 x
       grind)
    | exact superpose eq91218 eq91217
    | exact resolve eq91217 eq91218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91217
  have eq91381 : (σ (σ (σ y))) = (τ y) := by
    first
    | (have i₁ := eq91216 x
       have i₂ := eq91218 x
       grind)
    | exact superpose eq91218 eq91216
    | exact resolve eq91216 eq91218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91216
  have eq91385 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (τ y)) := by
    intro X0
    first
    | (have i₁ := eq91207 X0 x
       have i₂ := eq91218 x
       grind)
    | exact superpose eq91218 eq91207
    | exact resolve eq91207 eq91218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91207
  have eq91387 : ∀ X1 : G, (M.op X1 y) = (M.op (τ y) X1) := by
    intro X1
    first
    | (have i₁ := eq91201 x X1
       have i₂ := eq91218 x
       grind)
    | exact superpose eq91218 eq91201
    | exact resolve eq91201 eq91218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91201
  have eq91413 : ∀ X1 : G, (M.op y (M.op X1 (τ y))) = X1 := by
    intro X1
    first
    | (have i₁ := eq91165 x X1
       have i₂ := eq91272 x X1
       grind)
    | exact superpose eq91272 eq91165
    | exact resolve eq91165 eq91272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91165
  have eq91427 : (σ (σ y)) = (τ (τ y)) := by
    first
    | (have i₁ := eq91333
       have i₂ := eq9 (σ (σ y))
       grind)
    | exact superpose eq9 eq91333
    | exact resolve eq91333 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91333
  have eq91453 : (τ y) = (σ (τ y)) := by
    first
    | (have i₁ := eq91381
       have i₂ := eq91380
       grind)
    | exact superpose eq91380 eq91381
    | exact resolve eq91381 eq91380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91381
  have eq91478 : ∀ X1 : G, (M.op y (M.op X1 y)) = X1 := by
    intro X1
    first
    | (have i₁ := eq91413 X1
       have i₂ := eq91385 X1
       grind)
    | exact superpose eq91385 eq91413
    | exact resolve eq91413 eq91385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91413
  have eq91488 : (τ y) = (τ (τ y)) := by
    first
    | (have i₁ := eq91427
       have i₂ := eq91380
       grind)
    | exact superpose eq91380 eq91427
    | exact resolve eq91427 eq91380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91380 eq91427
  have eq91502 : y = (τ y) := by
    first
    | (have i₁ := eq91453
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq91453
    | exact resolve eq91453 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91453
  have eq92197 : y = (σ y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq91502
       grind)
    | exact superpose eq91502 eq10
    | exact resolve eq10 eq91502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92198 : ∀ X0 : G, (σ (k y X0)) = (k y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16 y X0
       have i₂ := eq91502
       grind)
    | exact superpose eq91502 eq16
    | exact resolve eq16 eq91502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq92790 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq92197
       grind)
    | exact superpose eq92197 eq14
    | exact resolve eq14 eq92197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92812 : ∀ X0 : G, (τ (M.op y y)) = X0 ∨ (σ (k y X0)) = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq300 y x
       have i₂ := eq92197
       grind)
    | exact superpose eq92197 eq300
    | exact resolve eq300 eq92197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq92813 : ∀ X0 : G, (σ (σ (σ y))) = X0 ∨ (σ (k y X0)) = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq92812 X0
       have i₂ := eq91308 y
       grind)
    | exact superpose eq91308 eq92812
    | (have j0 := eq92812 X0
       grind)
    | exact resolve eq92812 eq91308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91308 eq92812
  have eq92824 : ∀ X0 : G, (τ (τ y)) = X0 ∨ (σ (k y X0)) = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq92813 X0
       have i₂ := eq91335
       grind)
    | exact superpose eq91335 eq92813
    | (have j0 := eq92813 X0
       grind)
    | exact resolve eq92813 eq91335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92813
  have eq92835 : ∀ X0 : G, (τ y) = X0 ∨ (σ (k y X0)) = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq92824 X0
       have i₂ := eq91488
       grind)
    | exact superpose eq91488 eq92824
    | (have j0 := eq92824 X0
       grind)
    | exact resolve eq92824 eq91488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92824
  have eq92839 : ∀ X0 : G, (σ (k y X0)) = (M.op y (σ X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq92835 X0
       have i₂ := eq91502
       grind)
    | exact superpose eq91502 eq92835
    | (have j0 := eq92835 X0
       grind)
    | exact resolve eq92835 eq91502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92835
  have eq96559 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 (τ (σ y)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6900 x X0 X1
       have i₂ := eq91215 x
       grind)
    | exact superpose eq91215 eq6900
    | exact resolve eq6900 eq91215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6900 eq91215
  have eq96990 : ∀ X1 : G, (M.op (M.op X1 (τ (σ y))) (τ y)) = X1 := by
    intro X1
    first
    | (have i₁ := eq96559 x X1
       have i₂ := eq91272 x (M.op X1 (τ (σ y)))
       grind)
    | exact superpose eq91272 eq96559
    | exact resolve eq96559 eq91272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91272 eq96559
  have eq97367 : ∀ X1 : G, (M.op (M.op X1 (τ (σ y))) y) = X1 := by
    intro X1
    first
    | (have i₁ := eq96990 X1
       have i₂ := eq91385 (M.op X1 (τ (σ y)))
       grind)
    | exact superpose eq91385 eq96990
    | exact resolve eq96990 eq91385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91385 eq96990
  have eq97677 : ∀ X1 : G, (M.op (M.op X1 y) y) = X1 := by
    intro X1
    first
    | (have i₁ := eq97367 X1
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq97367
    | exact resolve eq97367 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97367
  have eq109143 : ∀ X0 : G, (M.op y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq91478 (M.op X0 y)
       have i₂ := eq97677 X0
       grind)
    | exact superpose eq97677 eq91478
    | exact resolve eq91478 eq97677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91478 eq97677
  have eq120277 : ∀ X0 : G, (σ (M.op X0 y)) = (k y (σ X0)) ∨ (M.op (τ y) (τ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq32 y X0
       have i₂ := eq91387 X0
       grind)
    | exact superpose eq91387 eq32
    | (have j0 := eq32 y X0
       grind)
    | exact resolve eq32 eq91387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq91387
  have eq120856 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ (M.op (τ y) (τ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq120277 X0
       have i₂ := eq92198 X0
       grind)
    | exact superpose eq92198 eq120277
    | (have j0 := eq120277 X0
       grind)
    | exact resolve eq120277 eq92198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92198 eq120277
  have eq121161 : ∀ X0 : G, (τ (τ (τ y))) = X0 ∨ (σ (k y X0)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq120856 X0
       have i₂ := eq91304 (τ y)
       grind)
    | exact superpose eq91304 eq120856
    | (have j0 := eq120856 X0
       grind)
    | exact resolve eq120856 eq91304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91304 eq120856
  have eq121297 : ∀ X0 : G, (σ (σ (σ y))) = X0 ∨ (σ (k y X0)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq121161 X0
       have i₂ := eq91332
       grind)
    | exact superpose eq91332 eq121161
    | (have j0 := eq121161 X0
       grind)
    | exact resolve eq121161 eq91332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91332 eq121161
  have eq121402 : ∀ X0 : G, (τ (τ y)) = X0 ∨ (σ (k y X0)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq121297 X0
       have i₂ := eq91335
       grind)
    | exact superpose eq91335 eq121297
    | (have j0 := eq121297 X0
       grind)
    | exact resolve eq121297 eq91335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91335 eq121297
  have eq121469 : ∀ X0 : G, (τ y) = X0 ∨ (σ (k y X0)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq121402 X0
       have i₂ := eq91488
       grind)
    | exact superpose eq91488 eq121402
    | (have j0 := eq121402 X0
       grind)
    | exact resolve eq121402 eq91488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121402
  have eq121527 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq121469 X0
       have i₂ := eq91502
       grind)
    | exact superpose eq91502 eq121469
    | (have j0 := eq121469 X0
       grind)
    | exact resolve eq121469 eq91502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121469
  have eq295331 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op y (σ X0)) ∨ y = X0 ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq121527 X0
       have i₂ := eq92839 X0
       grind)
    | exact superpose eq92839 eq121527
    | (have j0 := eq121527 X0
       have j1 := eq92839 X0
       grind)
    | exact resolve eq121527 eq92839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92839 eq121527
  have eq295341 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op y (σ X0)) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq295331 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295331
  have eq301791 : (M.op (σ x) y) ≠ (M.op y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq92790
       have i₂ := eq295341 x
       grind)
    | exact superpose eq295341 eq92790
    | (have j1 := eq295341 x
       grind)
    | exact resolve eq92790 eq295341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295341
  have eq301797 : (M.op y (σ x)) ≠ (M.op y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq301791
       have i₂ := eq109143 (σ x)
       grind)
    | exact superpose eq109143 eq301791
    | (have r₁ := eq301791
       have r₂ := eq109143 (σ x)
       grind)
    | exact resolve eq301791 eq109143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301791
  have eq301798 : x = y := by grind
  clear eq301797
  have eq301971 : x = (σ x) := by
    first
    | (have i₁ := eq92197
       have i₂ := eq301798
       grind)
    | exact superpose eq301798 eq92197
    | exact resolve eq92197 eq301798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92197
  have eq301975 : (σ (M.op x x)) ≠ (M.op (σ x) x) := by
    first
    | (have i₁ := eq92790
       have i₂ := eq301798
       grind)
    | exact superpose eq301798 eq92790
    | exact resolve eq92790 eq301798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92790
  have eq301985 : ∀ X0 : G, (M.op x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq109143 X0
       have i₂ := eq301798
       grind)
    | exact superpose eq301798 eq109143
    | exact resolve eq109143 eq301798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109143 eq301798
  have eq302096 : (σ (M.op x x)) ≠ (M.op x (σ x)) := by
    first
    | (have i₁ := eq301975
       have i₂ := eq301985 (σ x)
       grind)
    | exact superpose eq301985 eq301975
    | exact resolve eq301975 eq301985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301975 eq301985
  have eq302197 : (M.op x x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq302096
       have i₂ := eq301971
       grind)
    | exact superpose eq301971 eq302096
    | exact resolve eq302096 eq301971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301971 eq302096
  have eq302267 : (M.op x x) ≠ (τ (τ y)) := by
    first
    | (have i₁ := eq302197
       have i₂ := eq91302 x
       grind)
    | exact superpose eq91302 eq302197
    | exact resolve eq302197 eq91302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91302 eq302197
  have eq302310 : (M.op x x) ≠ (τ y) := by
    first
    | (have i₁ := eq302267
       have i₂ := eq91488
       grind)
    | exact superpose eq91488 eq302267
    | exact resolve eq302267 eq91488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91488 eq302267
  have eq302337 : y ≠ (M.op x x) := by
    first
    | (have i₁ := eq302310
       have i₂ := eq91502
       grind)
    | exact superpose eq91502 eq302310
    | exact resolve eq302310 eq91502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302310
  have eq302357 : y ≠ (τ y) := by
    first
    | (have i₁ := eq302337
       have i₂ := eq91218 x
       grind)
    | exact superpose eq91218 eq302337
    | exact resolve eq302337 eq91218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91218 eq302337
  have eq302367 : y ≠ y := by
    first
    | (have i₁ := eq302357
       have i₂ := eq91502
       grind)
    | exact superpose eq91502 eq302357
    | (have r₁ := eq302357
       have r₂ := eq91502
       grind)
    | exact resolve eq302357 eq91502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91502 eq302357
  have eq302368 : False := by grind
  exact eq302368

/-- `Equation703`: `x = y ◇ (y ◇ ((x ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_x_pyx_pxy_Equation703 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law703 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law703.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op (M.op X0 X0) X0))) = X0 := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq21 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq8 (M.op (M.op X0 X0) X0) (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       have i₂ := eq8 X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq30 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 (M.op X1 (M.op (M.op X0 X0) X0))) = (M.op (M.op X1 (M.op (M.op X0 X0) X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X1 (M.op (M.op X0 X0) X0))
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 X1 (M.op X1 (M.op (M.op X0 X0) X0))
       grind)
    | (have r₁ := eq11 X0 (M.op X0 (M.op (M.op X0 X0) X0))
       have r₂ := eq8 X0 X0
       grind)
    | exact resolve eq11 eq8
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
  clear eq20
  have eq40 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq41 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) := by
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
  clear eq15
  have eq63 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq40 x y
       grind)
    | exact superpose eq40 eq14
    | (have j1 := eq40 x y
       grind)
    | exact resolve eq14 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq84 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0)) (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0))) (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 (M.op (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0)) (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0)))
       have i₂ := eq21 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 : G, (k X0 (M.op X0 (M.op (M.op X0 X0) X0))) = (M.op (M.op X0 (M.op (M.op X0 X0) X0)) X0) := by
    intro X0
    first
    | (have j0 := eq30 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq234 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ (M.op (τ X1) (M.op (M.op X0 X0) X0)))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 (M.op (τ X0) (M.op (M.op X0 X0) X0))
       have i₂ := eq8 X0 (τ X0)
       grind)
    | exact superpose eq8 eq41
    | exact resolve eq41 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq275 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq63
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq63
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq63 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq276 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq275
  have eq871 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq21 (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0))
       have i₂ := eq84 X0
       grind)
    | exact superpose eq84 eq21
    | exact resolve eq21 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq872 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq84 X0
       grind)
    | exact superpose eq84 eq8
    | exact resolve eq8 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1140 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (τ (σ (M.op (τ (σ X1)) (M.op (M.op X0 X0) X0))))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27 X1 (σ (M.op (τ (σ X1)) (M.op (M.op X0 X0) X0)))
       have i₂ := eq234 X0 (σ X1)
       grind)
    | exact superpose eq234 eq27
    | (have j1 := eq234 (k X1 (τ (σ (M.op (τ (σ X1)) (M.op (M.op X0 X0) X0))))) (σ X0)
       grind)
    | exact resolve eq27 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq234
  have eq1162 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (M.op (τ (σ X1)) (M.op (M.op X0 X0) X0))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1140 X0 X1
       have i₂ := eq9 (M.op (τ (σ X1)) (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq9 eq1140
    | (have j0 := eq1140 (k X1 (M.op (τ (σ X1)) (M.op (M.op X0 X0) X0))) X0
       grind)
    | exact resolve eq1140 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq1188 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (M.op X1 (M.op (M.op X0 X0) X0))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1162 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq1162
    | (have j0 := eq1162 (k X1 (M.op X1 (M.op (M.op X0 X0) X0))) X0
       grind)
    | exact resolve eq1162 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162
  have eq1199 : ∀ X0 X1 : G, (k X1 (M.op X1 (M.op (M.op X0 X0) X0))) = X0 ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1188 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1188
    | (have j0 := eq1188 X0 X1
       grind)
    | exact resolve eq1188 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq1206 : ∀ X0 X1 : G, (k X1 (M.op X1 (M.op (M.op X0 X0) X0))) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1199 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq1199
    | (have j0 := eq1199 X0 X1
       grind)
    | exact resolve eq1199 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199
  have eq7892 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq872 X1 X2
       have i₂ := eq872 X1 X0
       grind)
    | exact superpose eq872 eq872
    | exact resolve eq872 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7901 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq871 X1
       have i₂ := eq872 X1 X0
       grind)
    | exact superpose eq872 eq871
    | exact resolve eq871 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq7902 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0
       have i₂ := eq872 X0 X1
       grind)
    | exact superpose eq872 eq84
    | exact resolve eq84 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq7904 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (M.op X1 X1) X1) X2
       have i₂ := eq872 X1 X0
       grind)
    | exact superpose eq872 eq8
    | exact resolve eq8 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq7959 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op (M.op X0 X0) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7892 X1 (M.op X2 (M.op (M.op X0 X0) X0)) X2
       have i₂ := eq8 X0 X2
       grind)
    | exact superpose eq8 eq7892
    | exact resolve eq7892 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7963 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X3 X1))) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7892 X2 (M.op X3 X1) X3
       have i₂ := eq7892 X3 X1 X0
       grind)
    | (have i₁ := eq7892 X2 (M.op X3 X1) X3
       have i₂ := eq7892 X0 X1 X3
       grind)
    | exact superpose eq7892 eq7892
    | exact resolve eq7892 eq7892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7971 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op X0 (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7892 X0 (σ y) (σ x)
       have i₂ := eq276
       grind)
    | exact superpose eq276 eq7892
    | exact resolve eq7892 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq8225 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2)))) = (M.op X3 (M.op X3 (M.op X4 (M.op X4 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7904 X4 X2 X3
       have i₂ := eq7904 X1 X2 X0
       grind)
    | exact superpose eq7904 eq7904
    | exact resolve eq7904 eq7904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8257 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7904 X1 X2 X1
       have i₂ := eq7892 X1 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq7904 X1 X2 X1
       have i₂ := eq7892 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq7892 eq7904
    | exact resolve eq7904 eq7892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8260 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X3) = (M.op (M.op (M.op X2 (M.op X2 X3)) (M.op X2 (M.op X2 X3))) (M.op X0 (M.op X0 (M.op X1 (M.op X1 (M.op X2 (M.op X2 X3))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7904 X2 X3 (M.op (M.op X2 (M.op X2 X3)) (M.op X2 (M.op X2 X3)))
       have i₂ := eq7904 X1 (M.op X2 (M.op X2 X3)) X0
       grind)
    | exact superpose eq7904 eq7904
    | exact resolve eq7904 eq7904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8264 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2)))))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3
       have i₂ := eq7904 X1 X2 X0
       grind)
    | exact superpose eq7904 eq8
    | exact resolve eq8 eq7904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8331 : ∀ X2 X3 : G, (M.op (M.op X3 X3) X3) = (M.op (M.op (M.op X2 (M.op X2 X3)) (M.op X2 (M.op X2 X3))) X3) := by
    intro X2 X3
    first
    | (have i₁ := eq8260 x x X2 X3
       have i₂ := eq8264 x X2 X3 x
       grind)
    | exact superpose eq8264 eq8260
    | exact resolve eq8260 eq8264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8260 eq8264
  have eq8698 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X1 (M.op (M.op X0 X0) X0))) = (M.op X2 (M.op X4 (M.op X4 (M.op X2 (M.op X3 (M.op X3 X0)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7963 X4 (M.op X2 (M.op X3 (M.op X3 X0))) X1 X2
       have i₂ := eq7904 X3 X0 X2
       grind)
    | exact superpose eq7904 eq7963
    | exact resolve eq7963 eq7904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8739 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op X0 (M.op X4 (M.op X4 X2))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq7963 X4 X2 x X0
       have i₂ := eq7963 X1 X2 x X0
       grind)
    | (have i₁ := eq7963 X0 X1 X0 X0
       have i₂ := eq7963 X0 X1 X2 X0
       grind)
    | exact superpose eq7963 eq7963
    | exact resolve eq7963 eq7963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8860 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 (M.op X3 X2)) (M.op X3 (M.op X3 X2))) (M.op X3 (M.op X3 X2))) = (M.op X4 (M.op X4 (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7904 X1 (M.op X3 (M.op X3 X2)) X4
       have i₂ := eq7963 X3 X2 X0 X1
       grind)
    | (have i₁ := eq7904 X2 (M.op X2 (M.op X3 X1)) X2
       have i₂ := eq7963 X0 X1 X2 X3
       grind)
    | exact superpose eq7963 eq7904
    | exact resolve eq7904 eq7963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8873 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (k X3 (M.op X3 (M.op X0 (M.op X0 (M.op (M.op (M.op X1 (M.op X1 X2)) (M.op X1 (M.op X1 X2))) X2))))) ∨ (M.op X1 (M.op X1 X2)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1206 (M.op X1 (M.op X1 X2)) X3
       have i₂ := eq7963 X1 X2 X0 (M.op (M.op X1 (M.op X1 X2)) (M.op X1 (M.op X1 X2)))
       grind)
    | exact superpose eq7963 eq1206
    | (have j0 := eq1206 (M.op X1 (M.op X1 X2)) (k X3 (M.op X3 (M.op X0 (M.op X0 (M.op (M.op (M.op X1 (M.op X1 X2)) (M.op X1 (M.op X1 X2))) X2)))))
       grind)
    | exact resolve eq1206 eq7963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206
  have eq8889 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (k X3 (M.op X3 (M.op X0 (M.op X0 (M.op (M.op X2 X2) X2))))) ∨ (M.op X1 (M.op X1 X2)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8873 X0 X1 X2 X3
       have i₂ := eq8331 X1 X2
       grind)
    | exact superpose eq8331 eq8873
    | (have j0 := eq8873 X0 X1 X2 (k X3 (M.op X3 (M.op X0 (M.op X0 (M.op (M.op X2 X2) X2)))))
       grind)
    | exact resolve eq8873 eq8331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8331 eq8873
  have eq8901 : ∀ X0 X1 X2 X4 : G, (M.op X4 (M.op X4 (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))))) = X2 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq8860 X0 X1 X2 x X4
       have i₂ := eq7902 x X2
       grind)
    | exact superpose eq7902 eq8860
    | exact resolve eq8860 eq7902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7902 eq8860
  have eq8930 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op X4 (M.op X4 (M.op X2 (M.op X3 (M.op X3 X0)))))) = X0 := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq8698 X0 x X2 X3 X4
       have i₂ := eq8 X0 x
       grind)
    | exact superpose eq8 eq8698
    | exact resolve eq8698 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8698
  have eq8934 : ∀ X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (k X3 (M.op X3 X2)) ∨ (M.op X1 (M.op X1 X2)) = X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq8889 x X1 X2 X3
       have i₂ := eq8 X2 x
       grind)
    | exact superpose eq8 eq8889
    | (have j0 := eq8889 x X1 X2 (k X3 (M.op X3 X2))
       grind)
    | exact resolve eq8889 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8889
  have eq9237 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X0) X0)) = (M.op X1 (M.op X1 (M.op X2 (M.op X2 (M.op X3 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7892 X1 (M.op X2 (M.op X2 (M.op X3 X0))) X3
       have i₂ := eq8257 X2 X3 X0
       grind)
    | exact superpose eq8257 eq7892
    | exact resolve eq7892 eq8257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10093 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op X2 (M.op X2 X1))) (M.op X0 (M.op X0 X1))) = (M.op X3 (M.op X4 (M.op X4 (M.op X3 (M.op X0 (M.op X0 X1)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8257 X4 X3 (M.op X0 (M.op X0 X1))
       have i₂ := eq8739 (M.op X0 (M.op X0 X1)) X0 X1 X2
       grind)
    | (have i₁ := eq8257 X4 X3 (M.op X0 (M.op X0 X1))
       have i₂ := eq8739 (M.op X0 (M.op X0 X1)) X2 X1 X0
       grind)
    | exact superpose eq8739 eq8257
    | exact resolve eq8257 eq8739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8739
  have eq10142 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op X2 (M.op X2 X1))) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10093 X0 X1 X2 x x
       have i₂ := eq8930 X1 x X0 x
       grind)
    | exact superpose eq8930 eq10093
    | exact resolve eq10093 eq8930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8930 eq10093
  have eq10513 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X1 (M.op X1 (M.op X0 (M.op X2 X3)))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8901 X0 X2 X3 X2
       have i₂ := eq7963 X1 (M.op X0 (M.op X2 X3)) X2 X0
       grind)
    | (have i₁ := eq8901 X0 X0 X2 X3
       have i₂ := eq7963 X0 (M.op X0 (M.op X0 X2)) X2 X3
       grind)
    | exact superpose eq7963 eq8901
    | exact resolve eq8901 eq7963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7963 eq8901
  have eq15434 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X1)) = (k X0 (M.op X0 X1)) ∨ (M.op X3 (M.op X3 X1)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7892 X2 X1 X3
       have i₂ := eq8934 X3 X1 X0
       grind)
    | exact superpose eq8934 eq7892
    | (have j1 := eq8934 X2 X1 X0
       grind)
    | exact resolve eq7892 eq8934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8934
  have eq18008 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X0) = X1 ∨ (M.op X2 (M.op X2 X1)) = (k X0 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 (M.op X1 X1)
       have i₂ := eq15434 X0 X1 X2 (M.op X1 X1)
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq15434 (M.op X1 (M.op (M.op X0 X0) X0)) X1 X2 x
       grind)
    | exact superpose eq15434 eq8
    | (have j1 := eq15434 X0 X1 X2 x
       grind)
    | exact resolve eq8 eq15434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20847 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) X1) = (M.op (M.op X0 X0) (M.op X2 (M.op X2 X0))) ∨ (k X1 (M.op X1 X0)) = (M.op X3 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8257 X2 (M.op X0 X0) X1
       have i₂ := eq18008 X1 X0 X3
       grind)
    | exact superpose eq18008 eq8257
    | (have j1 := eq18008 X1 X0 X3
       grind)
    | exact resolve eq8257 eq18008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8257 eq18008
  have eq21193 : ∀ X0 X1 X3 : G, (M.op (M.op X1 X1) X1) = X0 ∨ (k X1 (M.op X1 X0)) = (M.op X3 (M.op X3 X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq20847 X0 X1 x X3
       have i₂ := eq7901 x X0
       grind)
    | exact superpose eq7901 eq20847
    | (have j0 := eq20847 X0 X1 x X3
       grind)
    | exact resolve eq20847 eq7901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20847
  have eq22698 : ∀ X0 X1 X2 : G, (k X1 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op (M.op X0 X0) X0)))) ∨ (M.op X1 (M.op (M.op X0 X0) X0)) = (M.op (M.op X1 X1) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21193 (M.op X1 (M.op (M.op X0 X0) X0)) X1 X2
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq21193
    | (have j0 := eq21193 (M.op X1 (M.op (M.op X0 X0) X0)) X1 x
       grind)
    | exact resolve eq21193 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21193
  have eq23267 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X0)) = (M.op (M.op X1 X1) X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22698 X0 X1 x
       have i₂ := eq7959 X0 x X1
       grind)
    | exact superpose eq7959 eq22698
    | (have j0 := eq22698 X0 X1 x
       grind)
    | exact resolve eq22698 eq7959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7959 eq22698
  have eq27357 : ∀ X0 X1 X2 X3 X4 X6 : G, (M.op X1 (M.op X1 (M.op X2 (M.op X2 X3)))) = (M.op X4 (M.op X4 X0)) ∨ (k X0 (M.op X0 X3)) = (M.op X6 (M.op X6 X3)) := by
    intro X0 X1 X2 X3 X4 X6
    first
    | (have i₁ := eq8225 X1 X2 X3 X4 x
       have i₂ := eq15434 X0 X3 X6 x
       grind)
    | (have i₁ := eq8225 X0 X1 X2 X3 X4
       have i₂ := eq15434 (M.op X4 (M.op X4 X2)) X1 X2 X3
       grind)
    | exact superpose eq15434 eq8225
    | (have j1 := eq15434 X0 X3 X6 X3
       grind)
    | exact resolve eq8225 eq15434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8225 eq15434
  have eq89230 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0
       have i₂ := eq23267 X1 X0
       grind)
    | exact superpose eq23267 eq8
    | (have j1 := eq23267 X1 X0
       grind)
    | exact resolve eq8 eq23267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23267
  have eq89438 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0
       have i₂ := eq89230 X0 X1
       grind)
    | (have i₁ := eq101 X0
       have i₂ := eq89230 X0 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq89230 eq101
    | (have j1 := eq89230 X1 X0
       grind)
    | exact resolve eq101 eq89230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq89230
  have eq89711 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq89438 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89438
  have eq89750 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2)))) ≠ (M.op X2 (M.op X2 X2)) ∨ (M.op X2 (M.op X2 X2)) = (k X2 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq89711 X2 (M.op X2 X2)
       have i₂ := eq7904 X1 X2 X0
       grind)
    | exact superpose eq7904 eq89711
    | (have j0 := eq89711 X2 (M.op X2 X2)
       grind)
    | exact resolve eq89711 eq7904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7904
  have eq89754 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq89711 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89711
  have eq89757 : ∀ X2 : G, (M.op X2 (M.op X2 X2)) = (k X2 (M.op X2 X2)) := by
    intro X2
    first
    | (have j0 := eq89750 x x X2
       have j1 := eq27357 X2 x X2 X2 x X2
       grind)
    | (have r₁ := eq89750 x X2 x
       have r₂ := eq27357 x x X2 x x x
       grind)
    | (have r₁ := eq89750 x x (M.op X2 (M.op X2 x))
       have r₂ := eq27357 (M.op x (M.op x (M.op X2 (M.op X2 x)))) (M.op X2 (M.op X2 x)) X2 x x x
       grind)
    | exact resolve eq89750 eq27357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27357 eq89750
  have eq89911 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq89754 (σ X0)
       grind)
    | exact superpose eq89754 eq13
    | exact resolve eq13 eq89754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89940 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq89754 (τ X0)
       grind)
    | exact superpose eq89754 eq31
    | exact resolve eq31 eq89754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90028 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq89940 X0
       have i₂ := eq89754 X0
       grind)
    | exact superpose eq89754 eq89940
    | exact resolve eq89940 eq89754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89940
  have eq90056 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq89911 X0
       have i₂ := eq89754 X0
       grind)
    | exact superpose eq89754 eq89911
    | exact resolve eq89911 eq89754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89754 eq89911
  have eq90534 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (τ X0))) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7892 X1 (τ X0) (τ X0)
       have i₂ := eq90028 X0
       grind)
    | exact superpose eq90028 eq7892
    | exact resolve eq7892 eq90028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91034 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0))) = (M.op X1 (M.op X1 (M.op X2 (M.op X2 (σ (M.op X0 X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9237 (σ X0) X1 X2 (σ X0)
       have i₂ := eq90056 X0
       grind)
    | exact superpose eq90056 eq9237
    | exact resolve eq9237 eq90056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91266 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (k (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq89757 (τ X0)
       have i₂ := eq90028 X0
       grind)
    | exact superpose eq90028 eq89757
    | exact resolve eq89757 eq90028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90028
  have eq91357 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq91266 X0
       have i₂ := eq31 (M.op X0 X0) X0
       grind)
    | exact superpose eq31 eq91266
    | exact resolve eq91266 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq91266
  have eq91388 : ∀ X0 : G, (τ (M.op X0 (M.op X0 X0))) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq91357 X0
       have i₂ := eq89757 X0
       grind)
    | exact superpose eq89757 eq91357
    | exact resolve eq91357 eq89757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89757 eq91357
  have eq93974 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (τ X0))) = (τ (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq90534 X0 X1
       have i₂ := eq91388 X0
       grind)
    | exact superpose eq91388 eq90534
    | exact resolve eq90534 eq91388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90534 eq91388
  have eq94110 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (τ X1))) = (τ (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq93974 X1 X2
       have i₂ := eq7892 X1 X1 X0
       grind)
    | (have i₁ := eq93974 X1 X2
       have i₂ := eq7892 X0 X1 X1
       grind)
    | exact superpose eq7892 eq93974
    | exact resolve eq93974 eq7892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7892
  have eq94143 : ∀ X0 : G, (τ (M.op (σ x) (σ x))) = (M.op X0 (M.op X0 (τ (σ y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq93974 (σ y) X0
       have i₂ := eq7971 (σ y)
       grind)
    | exact superpose eq7971 eq93974
    | exact resolve eq93974 eq7971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7971 eq93974
  have eq94483 : ∀ X0 : G, (τ (M.op (σ x) (σ x))) = (M.op X0 (M.op X0 y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq94143 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq94143
    | exact resolve eq94143 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94143
  have eq94563 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (τ (σ (M.op x x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq94483 X0
       have i₂ := eq90056 x
       grind)
    | exact superpose eq90056 eq94483
    | exact resolve eq94483 eq90056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94483
  have eq94599 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op X0 y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq94563 X0
       have i₂ := eq9 (M.op x x)
       grind)
    | exact superpose eq9 eq94563
    | exact resolve eq94563 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94563
  have eq94642 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = (τ (M.op X2 (M.op X2 (σ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq94110 X2 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq94110
    | exact resolve eq94110 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94110
  have eq96822 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 (σ (M.op (M.op X1 X1) X1))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7901 (M.op X1 X1) X1
       have i₂ := eq94642 (M.op (M.op X1 X1) X1) (M.op X1 X1) X0
       grind)
    | exact superpose eq94642 eq7901
    | exact resolve eq7901 eq94642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7901
  have eq96844 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X0 X1))) = (M.op X2 (M.op X2 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X2 (M.op X2 (σ X1)))
       have i₂ := eq94642 X1 X0 X2
       grind)
    | exact superpose eq94642 eq10
    | exact resolve eq10 eq94642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94642
  have eq99469 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op (M.op X0 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 (M.op X1 (σ (M.op (M.op X0 X0) X0))))
       have i₂ := eq96822 X1 X0
       grind)
    | exact superpose eq96822 eq10
    | exact resolve eq10 eq96822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96822
  have eq100371 : ∀ X0 X2 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (M.op (σ X0) (M.op X2 (M.op X2 (σ (M.op (M.op X0 X0) X0))))) (σ X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq10142 x (σ (M.op (M.op X0 X0) X0)) X2
       have i₂ := eq99469 X0 x
       grind)
    | exact superpose eq99469 eq10142
    | exact resolve eq10142 eq99469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10142
  have eq100483 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq100371 X0 x
       have i₂ := eq99469 X0 x
       grind)
    | exact superpose eq99469 eq100371
    | exact resolve eq100371 eq99469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100371
  have eq100511 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq100483 X0
       have i₂ := eq90056 X0
       grind)
    | exact superpose eq90056 eq100483
    | exact resolve eq100483 eq90056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90056 eq100483
  have eq102022 : ∀ X0 X1 : G, y = (M.op X0 (M.op X0 (M.op X1 (M.op X1 (M.op x x))))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq10513 X0 X1 X0 y
       have i₂ := eq94599 X0
       grind)
    | exact superpose eq94599 eq10513
    | exact resolve eq10513 eq94599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94599
  have eq102119 : y = (M.op x (M.op (M.op x x) x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq102022 x x
       have i₂ := eq9237 x x x x
       grind)
    | exact superpose eq9237 eq102022
    | exact resolve eq102022 eq9237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9237 eq102022
  have eq103345 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8 x x
       have i₂ := eq102119
       grind)
    | exact superpose eq102119 eq8
    | exact resolve eq8 eq102119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102119
  have eq103416 : x = (M.op x y) := by grind
  clear eq103345
  have eq103575 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq96844 x y X0
       have i₂ := eq103416
       grind)
    | exact superpose eq103416 eq96844
    | exact resolve eq96844 eq103416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96844
  have eq105683 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op X0 (M.op X1 (M.op X1 (σ (M.op x x)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq10513 X0 X1 X0 (σ y)
       have i₂ := eq103575 X0
       grind)
    | exact superpose eq103575 eq10513
    | exact resolve eq10513 eq103575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10513 eq103575
  have eq105854 : (σ y) = (M.op (σ x) (M.op (σ (M.op x x)) (σ x))) := by
    first
    | (have i₁ := eq105683 x x
       have i₂ := eq91034 x x x
       grind)
    | exact superpose eq91034 eq105683
    | exact resolve eq105683 eq91034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91034 eq105683
  have eq106001 : (σ y) = (M.op (σ x) (σ (M.op (M.op x x) x))) := by
    first
    | (have i₁ := eq105854
       have i₂ := eq100511 x
       grind)
    | exact superpose eq100511 eq105854
    | exact resolve eq105854 eq100511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100511 eq105854
  have eq107502 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq99469 x (σ x)
       have i₂ := eq106001
       grind)
    | exact superpose eq106001 eq99469
    | exact resolve eq99469 eq106001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99469 eq106001
  have eq107659 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq107502
       grind)
    | exact superpose eq107502 eq14
    | exact resolve eq14 eq107502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107502
  have eq107899 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq107659
       have i₂ := eq103416
       grind)
    | exact superpose eq103416 eq107659
    | exact resolve eq107659 eq103416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103416 eq107659
  have eq107900 : False := by grind
  exact eq107900
