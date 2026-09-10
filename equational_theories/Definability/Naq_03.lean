import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_y_pyx_x_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
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
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) X3) = X3 := by
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
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq48 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq48
    | (have j0 := eq48 (σ X0) (σ X1)
       grind)
    | exact resolve eq48 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq36 (τ X0)
       grind)
    | exact superpose eq36 eq19
    | exact resolve eq19 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq92 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq91 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq91
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq100 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq92 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq92
    | exact resolve eq92 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq92
  have eq104 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq100 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq100
    | exact resolve eq100 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq142 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq25 (M.op X0 X0) x x X3
       have i₂ := eq24 X0 x x (M.op X0 X0)
       grind)
    | exact superpose eq24 eq25
    | exact resolve eq25 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq25
  have eq179 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq61 y x
       grind)
    | exact superpose eq61 eq16
    | (have j1 := eq61 y x
       grind)
    | exact resolve eq16 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq310 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq142 (σ X0) X1
       have i₂ := eq104 X0
       grind)
    | exact superpose eq104 eq142
    | exact resolve eq142 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq920 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq179
       have i₂ := eq104 y
       grind)
    | exact superpose eq104 eq179
    | exact resolve eq179 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq179
  have eq921 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq920
       have i₂ := eq48 y x
       grind)
    | exact superpose eq48 eq920
    | (have j1 := eq48 y x
       grind)
    | exact resolve eq920 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq920
  have eq922 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq921
  have eq1538 : ∀ X0 : G, (σ x) = (σ (M.op y y)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq142 y X0
       have i₂ := eq922
       grind)
    | exact superpose eq922 eq142
    | exact resolve eq142 eq922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq1562 : ∀ X0 : G, (M.op y y) = (τ (σ x)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1538 X0
       grind)
    | exact superpose eq1538 eq10
    | (have j1 := eq1538 X0
       grind)
    | exact resolve eq10 eq1538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538
  have eq1595 : ∀ X0 : G, x = (M.op y y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1562 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1562
    | (have j0 := eq1562 X0
       grind)
    | exact resolve eq1562 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1562
  have eq1605 : ∀ X0 X1 : G, (M.op x X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq142 y X0
       have i₂ := eq1595 X1
       grind)
    | exact superpose eq1595 eq142
    | (have j1 := eq1595 X0
       grind)
    | exact resolve eq142 eq1595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq1595
  have eq1748 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1605 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1605
  have eq1749 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1748 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1748
  have eq1767 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq310 x X0
       have i₂ := eq1749 x
       grind)
    | exact superpose eq1749 eq310
    | exact resolve eq310 eq1749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq1913 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1767 (σ y)
       grind)
    | exact superpose eq1767 eq16
    | exact resolve eq16 eq1767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1767
  have eq1964 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1913
       have i₂ := eq1749 y
       grind)
    | exact superpose eq1749 eq1913
    | exact resolve eq1913 eq1749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1749 eq1913
  have eq1965 : False := by grind
  exact eq1965

/-- `Equation3272`: `x ◇ x = y ◇ (x ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation3272 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3272 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3272.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
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
  have eq50 : x ≠ (M.op x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (k x y) := by
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
  have eq69 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq93
    | exact resolve eq93 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq101
    | exact resolve eq101 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq105 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq103
    | exact resolve eq103 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq105
    | exact resolve eq105 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq610 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq106 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq611 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq610
    | exact resolve eq610 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq614 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq611
       have r₂ := eq27
       grind)
    | exact resolve eq611 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq616 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq614
    | exact resolve eq614 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq618 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq616
    | exact resolve eq616 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq620 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq618 eq69
    | (have r₁ := eq69
       have r₂ := eq618
       grind)
    | exact resolve eq69 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq623 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq618
  have eq624 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq620
  have eq671 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq624
       have r₂ := eq623
       grind)
    | exact resolve eq624 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623 eq624
  have eq675 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq671 eq55
    | exact resolve eq55 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq683 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq675
    | exact resolve eq675 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq675
  have eq687 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq683
       have r₂ := eq68
       grind)
    | exact resolve eq683 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq694 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq687
       grind)
    | exact superpose eq687 eq44
    | exact resolve eq44 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq687
       grind)
    | exact superpose eq687 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq696 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq695
  have eq698 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq696
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq696
    | exact resolve eq696 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq699 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq698
  have eq700 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq694
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq694
    | exact resolve eq694 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq703 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq699
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq699
    | exact resolve eq699 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq706 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq703 eq51
    | (have r₁ := eq51
       have r₂ := eq703
       grind)
    | exact resolve eq51 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq708 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq706
  have eq734 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq700 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq735 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq734
  have eq739 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq735
    | exact resolve eq735 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq740 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq739
  have eq745 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq740
    | exact resolve eq740 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq750 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq745 eq27
    | exact resolve eq27 eq745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq862 : (τ (σ y)) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq708 eq55
    | exact resolve eq55 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq873 : y = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq862
    | exact resolve eq862 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq876 : y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq873
       have r₂ := eq50
       grind)
    | exact resolve eq873 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq882 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq876
       grind)
    | exact superpose eq876 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876
  have eq883 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq882
  have eq885 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq883
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq883
    | exact resolve eq883 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883
  have eq886 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq885
  have eq890 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq886
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq886
    | exact resolve eq886 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq886
  have eq892 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq890 eq20
    | exact resolve eq20 eq890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq895 : y ≠ y ∨ x = y ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq890 eq68
    | (have r₁ := eq68
       have r₂ := eq890
       grind)
    | exact resolve eq68 eq890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq903 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq890
  have eq904 : x = y ∨ x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq895
  have eq914 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq892
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq892
    | exact resolve eq892 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq931 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq914 eq750
    | (have r₁ := eq750
       have r₂ := eq914
       grind)
    | exact resolve eq750 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750 eq914
  have eq934 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq931
  have eq935 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq934
  have eq997 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq935 eq51
    | (have r₁ := eq51
       have r₂ := eq935
       grind)
    | exact resolve eq51 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq935
  have eq998 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq997
  have eq1072 : (τ (σ y)) = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq998 eq55
    | exact resolve eq55 eq998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq998
  have eq1087 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1072
    | exact resolve eq1072 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1072
  have eq1090 : y = (k x y) := by
    first
    | (have r₁ := eq1087
       have r₂ := eq50
       grind)
    | exact resolve eq1087 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1087
  have eq1139 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1090
       grind)
    | exact superpose eq1090 eq44
    | exact resolve eq44 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq1144 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1139
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1139
    | exact resolve eq1139 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1139
  have eq1157 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1144 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1158 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1157
  have eq1160 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1158
    | exact resolve eq1158 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158
  have eq1163 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1160
    | exact resolve eq1160 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1160
  have eq1167 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1163 eq69
    | (have r₁ := eq69
       have r₂ := eq1163
       grind)
    | exact resolve eq69 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq1170 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1163
  have eq1171 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1167
  have eq1172 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1144 eq1171
    | exact resolve eq1171 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144 eq1171
  have eq1173 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1172
  have eq1273 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1173
       have r₂ := eq1170
       grind)
    | exact resolve eq1173 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170 eq1173
  have eq1277 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1273 eq27
    | exact resolve eq27 eq1273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1273
  have eq2339 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq904
       have r₂ := eq903
       grind)
    | exact resolve eq904 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904
  have eq2340 : x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2339
       have i₂ := eq1090
       grind)
    | exact superpose eq1090 eq2339
    | exact resolve eq2339 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090 eq2339
  have eq2341 : x = (M.op x y) := by
    first
    | (have r₁ := eq2340
       have r₂ := eq903
       grind)
    | exact resolve eq2340 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903 eq2340
  have eq2343 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2341 eq20
    | exact resolve eq20 eq2341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2341
  have eq2370 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2343
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2343
    | exact resolve eq2343 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2343
  have eq2372 : False := by grind
  exact eq2372

/-- `Equation3481`: `x ◇ x = y ◇ ((y ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_pyx_pxy_Equation3481 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3481 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3481.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq29
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq195 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq77 x y
       grind)
    | exact superpose eq77 eq16
    | (have j1 := eq77 y y
       grind)
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq77 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq13 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq77 X0 X0
       grind)
    | (have r₁ := eq12 (σ X1) X1
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) X1
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq77 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq202 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq201 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq204 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq199 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq205 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq198 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq206 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq204 X0 X1
       have j1 := eq12 (σ X0) X1
       grind)
    | (have r₁ := eq204 X0 X1
       have r₂ := eq12 (σ X0) X1
       grind)
    | exact resolve eq204 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq207 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq205 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq205 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq205 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq205 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq210 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq207 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq207 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq207 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq281 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq210 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq210
    | (have j0 := eq210 (τ X0) X1
       grind)
    | exact resolve eq210 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq283 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq281 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq281
    | (have j0 := eq281 X0 X1
       grind)
    | exact resolve eq281 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq286 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq283 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq283
    | (have j0 := eq283 X0 X1
       grind)
    | exact resolve eq283 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq521 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq195
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq195
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq195 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq522 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq521
  have eq2573 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq78 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq2574 : ∀ X0 : G, (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2573 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2573
  have eq2578 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2574 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2574
    | (have j0 := eq2574 X0
       grind)
    | exact resolve eq2574 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2574
  have eq2581 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2578 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2578
    | exact resolve eq2578 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2578
  have eq2616 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2581 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq2581
    | (have j0 := eq2581 X0
       grind)
    | exact resolve eq2581 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq2581
  have eq2620 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq2616 X0
       grind)
    | exact superpose eq2616 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq2616 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq2616 X0
       grind)
    | exact resolve eq12 eq2616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2616
  have eq2635 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2620 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2620
  have eq2703 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq2635 X0 X1
       grind)
    | exact superpose eq2635 eq11
    | (have j1 := eq2635 X0 X1
       grind)
    | exact resolve eq11 eq2635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2635
  have eq2786 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2703 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq2703
    | (have j0 := eq2703 X0 X0
       grind)
    | exact resolve eq2703 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2703
  have eq2881 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2786 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2786
  have eq2882 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2881 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2881
  have eq2992 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq202 X0
       have i₂ := eq2882 X0
       grind)
    | exact superpose eq2882 eq202
    | (have j0 := eq202 X0
       grind)
    | exact resolve eq202 eq2882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq2993 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq206 X0 X1
       have i₂ := eq2882 X0
       grind)
    | exact superpose eq2882 eq206
    | (have j0 := eq206 X0 X1
       grind)
    | exact resolve eq206 eq2882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq2994 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq210 X0 X1
       have i₂ := eq2882 X0
       grind)
    | exact superpose eq2882 eq210
    | (have j0 := eq210 X0 X1
       grind)
    | exact resolve eq210 eq2882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq3002 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq286 X0 X1
       have i₂ := eq2882 X0
       grind)
    | exact superpose eq2882 eq286
    | (have j0 := eq286 X0 X1
       grind)
    | exact resolve eq286 eq2882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq3026 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq2882 (σ X0)
       grind)
    | exact superpose eq2882 eq15
    | exact resolve eq15 eq2882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3084 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3026 X0
       have i₂ := eq2882 X0
       grind)
    | exact superpose eq2882 eq3026
    | exact resolve eq3026 eq2882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2882 eq3026
  have eq3485 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2992 y
       have i₂ := eq522
       grind)
    | exact superpose eq522 eq2992
    | (have j0 := eq2992 y
       grind)
    | exact resolve eq2992 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq3490 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq3485
  have eq3491 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq3490
  have eq3501 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3491
       have i₂ := eq3084 y
       grind)
    | exact superpose eq3084 eq3491
    | exact resolve eq3491 eq3084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3491
  have eq3513 : x = (M.op x x) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3501
       have i₂ := eq3084 x
       grind)
    | exact superpose eq3084 eq3501
    | exact resolve eq3501 eq3084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3501
  have eq5388 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2992 x
       have i₂ := eq3513
       grind)
    | exact superpose eq3513 eq2992
    | (have j0 := eq2992 x
       grind)
    | (have r₁ := eq2992 y
       have r₂ := eq3513
       grind)
    | (have r₁ := eq2992 x
       have r₂ := eq3513
       grind)
    | exact resolve eq2992 eq3513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5390 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq2994 x X0
       have i₂ := eq3513
       grind)
    | exact superpose eq3513 eq2994
    | (have j0 := eq2994 x X0
       grind)
    | (have r₁ := eq2994 y x
       have r₂ := eq3513
       grind)
    | (have r₁ := eq2994 x x
       have r₂ := eq3513
       grind)
    | exact resolve eq2994 eq3513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3513
  have eq5407 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq5390 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5390
  have eq5409 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq5388
  have eq5415 : ∀ X0 : G, (σ y) = (σ (M.op y y)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq5407 X0
       have j1 := eq2994 x X0
       grind)
    | (have r₁ := eq5407 X0
       have r₂ := eq2994 y x
       grind)
    | (have r₁ := eq5407 X0
       have r₂ := eq2994 x x
       grind)
    | exact resolve eq5407 eq2994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2994 eq5407
  have eq5417 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have j1 := eq2992 x
       grind)
    | (have r₁ := eq5409
       have r₂ := eq2992 y
       grind)
    | (have r₁ := eq5409
       have r₂ := eq2992 x
       grind)
    | exact resolve eq5409 eq2992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2992 eq5409
  have eq5418 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5417
       have i₂ := eq3084 x
       grind)
    | exact superpose eq3084 eq5417
    | exact resolve eq5417 eq3084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3084 eq5417
  have eq5536 : (M.op y y) = (τ (σ y)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq5418
       grind)
    | exact superpose eq5418 eq10
    | exact resolve eq10 eq5418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5418
  have eq5597 : y = (M.op y y) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5536
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5536
    | exact resolve eq5536 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5536
  have eq5605 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k y X0) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq5597
       grind)
    | exact superpose eq5597 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq5597
       grind)
    | exact resolve eq12 eq5597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5597
  have eq5635 : ∀ X0 : G, (σ x) = (σ (M.op x x)) ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq5605 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5605
  have eq5974 : ∀ X0 : G, (M.op x x) = (τ (σ x)) ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq5635 X0
       grind)
    | exact superpose eq5635 eq10
    | (have j1 := eq5635 X0
       grind)
    | exact resolve eq10 eq5635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5635
  have eq6035 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq5974 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5974
    | (have j0 := eq5974 X0
       grind)
    | exact resolve eq5974 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5974
  have eq6129 : ∀ X0 X1 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) ∨ (M.op X1 y) = (k y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3002 x X0
       have i₂ := eq6035 X1
       grind)
    | exact superpose eq6035 eq3002
    | (have j0 := eq3002 x X0
       have j1 := eq6035 X1
       grind)
    | (have r₁ := eq3002 x X1
       have r₂ := eq6035 X0
       grind)
    | exact resolve eq3002 eq6035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3002 eq6035
  have eq6140 : ∀ X0 X1 : G, (M.op x X0) = (k X0 x) ∨ (M.op X1 y) = (k y X1) := by
    intro X0 X1
    first
    | (have j0 := eq6129 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6129
  have eq6820 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have j0 := eq6140 y x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6140
  have eq6821 : (M.op x y) = (k y x) := by grind
  clear eq6820
  have eq7839 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (k X1 (σ x)) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2993 y X0
       have i₂ := eq5415 X1
       grind)
    | exact superpose eq5415 eq2993
    | (have j0 := eq2993 y X0
       have j1 := eq5415 X1
       grind)
    | (have r₁ := eq2993 y X1
       have r₂ := eq5415 X0
       grind)
    | exact resolve eq2993 eq5415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2993 eq5415
  have eq7873 : ∀ X0 X1 : G, (k X1 (σ x)) = (M.op (σ x) X1) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq7839 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7839
  have eq74944 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have j0 := eq7873 (σ x) (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7873
  have eq74945 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq74944
  have eq74946 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq74945
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq74945
    | exact resolve eq74945 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74945
  have eq75007 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74946
       have i₂ := eq6821
       grind)
    | exact superpose eq6821 eq74946
    | exact resolve eq74946 eq6821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6821 eq74946
  have eq75022 : False := by grind
  exact eq75022

/-- `Equation3487`: `x ◇ x = y ◇ ((y ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_x_pyx_Equation3487 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3487 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3487.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X2) X0)) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq176 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 (M.op (M.op X2 x) X0)
       have i₂ := eq16 X0 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq578 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X1 X1) X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op (M.op X1 X1) X0) X2 x
       have i₂ := eq178 X1 X0 (M.op X2 x)
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq579 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq578 X0 x X2
       have i₂ := eq178 x X0 (M.op (M.op x x) X0)
       grind)
    | exact superpose eq178 eq578
    | exact resolve eq578 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq578
  have eq614 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X0) X1
       have i₂ := eq579 X0 (M.op X0 X0)
       grind)
    | exact superpose eq579 eq13
    | (have j0 := eq13 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X1
       have r₂ := eq579 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq623 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq614 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq2775 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq176 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq176
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2817 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2824 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2857 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2775 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2775
  have eq9844 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq2817
       grind)
    | exact superpose eq2817 eq39
    | exact resolve eq39 eq2817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq2817
  have eq9845 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9844
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9844
    | exact resolve eq9844 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9844
  have eq9848 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq9845
    | exact resolve eq9845 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9845
  have eq16117 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq2857 eq176
    | (have j1 := eq2857 X0
       grind)
    | exact resolve eq176 eq2857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq2857
  have eq16180 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq16117 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq16117 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq16117 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16117
  have eq16330 : ∀ X0 X1 : G, (k X0 X0) = (M.op X1 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq579 X0 x
       have i₂ := eq16180 X0
       grind)
    | exact superpose eq16180 eq579
    | exact resolve eq579 eq16180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq16331 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (k (k X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq623 X0 X1
       have i₂ := eq16180 X0
       grind)
    | exact superpose eq16180 eq623
    | exact resolve eq623 eq16180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq16932 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op X1 (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16330 (σ X1) X1
       have i₂ := eq10 X1 X1
       grind)
    | exact superpose eq10 eq16330
    | exact resolve eq16330 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19888 : ∀ X0 X1 : G, (M.op (σ (k X0 X0)) X1) = (k (σ (k X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16331 (σ X1) X1
       have i₂ := eq10 X1 X1
       grind)
    | exact superpose eq10 eq16331
    | exact resolve eq16331 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61677 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq9848 eq2824
    | exact resolve eq2824 eq9848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2824 eq9848
  have eq61686 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq61677
       have r₂ := eq27
       grind)
    | exact resolve eq61677 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61677
  have eq61693 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq61686
       have i₂ := eq16180 sF2
       grind)
    | exact superpose eq16180 eq61686
    | exact resolve eq61686 eq16180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61686
  have eq61698 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq61693
       have i₂ := eq16180 sF3
       grind)
    | exact superpose eq16180 eq61693
    | exact resolve eq61693 eq16180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61693
  have eq61703 : x = (k x x) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq61698
       have i₂ := eq16180 x
       grind)
    | exact superpose eq16180 eq61698
    | exact resolve eq61698 eq16180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61698
  have eq61706 : (σ y) = (k (σ y) (σ y)) ∨ x = (k x x) ∨ y = (k y y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq61703
       have i₂ := eq16180 y
       grind)
    | exact superpose eq16180 eq61703
    | exact resolve eq61703 eq16180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16180 eq61703
  have eq62935 : (τ (σ y)) = (k (τ (σ y)) y) ∨ x = (k x x) ∨ y = (k y y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq61706 eq152
    | exact resolve eq152 eq61706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq61706
  have eq63065 : y = (k y y) ∨ x = (k x x) ∨ y = (k y y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq31 eq62935
    | exact resolve eq62935 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq62935
  have eq63066 : (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ y = (k y y) := by grind
  clear eq63065
  have eq63099 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (k x x) ∨ y = (k y y) := by
    first
    | exact superpose eq63066 eq141
    | exact resolve eq141 eq63066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq63066
  have eq63228 : x = (k x x) ∨ x = (k x x) ∨ y = (k y y) := by
    first
    | exact superpose eq29 eq63099
    | exact resolve eq63099 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq63099
  have eq63229 : y = (k y y) ∨ x = (k x x) := by grind
  clear eq63228
  have eq63271 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq16330 y x
       have i₂ := eq63229
       grind)
    | exact superpose eq63229 eq16330
    | exact resolve eq16330 eq63229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16330
  have eq63297 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq16932 y x
       have i₂ := eq63229
       grind)
    | exact superpose eq63229 eq16932
    | exact resolve eq16932 eq63229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16932 eq63229
  have eq63366 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq63297 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq63297
    | (have j0 := eq63297 X0
       grind)
    | exact resolve eq63297 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63297
  have eq63488 : x = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq63271 x
       grind)
    | exact superpose eq63271 eq18
    | (have j1 := eq63271 x
       grind)
    | exact resolve eq18 eq63271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63271
  have eq63743 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16331 x x
       have i₂ := eq63488
       grind)
    | exact superpose eq63488 eq16331
    | exact resolve eq16331 eq63488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63770 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq19888 x x
       have i₂ := eq63488
       grind)
    | exact superpose eq63488 eq19888
    | exact resolve eq19888 eq63488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63488
  have eq63834 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq63770 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq63770
    | (have j0 := eq63770 X0
       grind)
    | exact resolve eq63770 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63770
  have eq64680 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq63366 eq26
    | (have j1 := eq63366 (σ x)
       grind)
    | exact resolve eq26 eq63366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63366
  have eq64969 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16331 x x
       have i₂ := eq64680
       grind)
    | exact superpose eq64680 eq16331
    | exact resolve eq16331 eq64680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16331
  have eq64996 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19888 x x
       have i₂ := eq64680
       grind)
    | exact superpose eq64680 eq19888
    | exact resolve eq19888 eq64680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19888 eq64680
  have eq65060 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq64996 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq64996
    | (have j0 := eq64996 X0
       grind)
    | exact resolve eq64996 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64996
  have eq66254 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq63743 y
       grind)
    | exact superpose eq63743 eq18
    | (have j1 := eq63743 y
       grind)
    | exact resolve eq18 eq63743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63743
  have eq66573 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq66254
       grind)
    | exact superpose eq66254 eq40
    | exact resolve eq40 eq66254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq66254
  have eq66575 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq66573
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq66573
    | exact resolve eq66573 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq66573
  have eq66579 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq66575
    | exact resolve eq66575 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66575
  have eq68923 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq63834 eq26
    | (have j1 := eq63834 (σ y)
       grind)
    | exact resolve eq26 eq63834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63834
  have eq69102 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq66579 eq68923
    | exact resolve eq68923 eq66579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66579 eq68923
  have eq69220 : y = (M.op x y) := by
    first
    | (have r₁ := eq69102
       have r₂ := eq27
       grind)
    | exact resolve eq69102 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69102
  have eq69280 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq69220
       grind)
    | exact superpose eq69220 eq18
    | exact resolve eq18 eq69220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq69281 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq69220
       grind)
    | exact superpose eq69220 eq24
    | exact resolve eq24 eq69220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq69220
  have eq69314 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq69281 eq20
    | exact resolve eq20 eq69281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69281
  have eq71167 : (M.op x y) = (k x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq69280
       have i₂ := eq64969 sF0
       grind)
    | exact superpose eq64969 eq69280
    | exact resolve eq69280 eq64969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64969 eq69280
  have eq71503 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq71167 eq35
    | exact resolve eq35 eq71167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq71167
  have eq71509 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq71503
    | exact resolve eq71503 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq71503
  have eq71514 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq69314 eq71509
    | exact resolve eq71509 eq69314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71509
  have eq73705 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq65060 eq26
    | (have j1 := eq65060 (σ y)
       grind)
    | exact resolve eq26 eq65060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq65060
  have eq73890 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq71514 eq73705
    | exact resolve eq73705 eq71514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71514 eq73705
  have eq73891 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq73890
  have eq74013 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq73891 eq27
    | exact resolve eq27 eq73891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq73891
  have eq74116 : False := by grind
  exact eq74116

/-- `Equation3491`: `x ◇ x = y ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_y_pxx_pxy_Equation3491 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3491 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3491.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X0) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
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
  have eq21 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq34 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X0) (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) X0) X2 x
       have i₂ := eq9 X0 (M.op x (M.op (M.op X1 X0) X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq34 X0 x X2
       have i₂ := eq9 X0 (M.op (M.op x X0) X0) x
       grind)
    | (have i₁ := eq34 X0 x X2
       have i₂ := eq9 (M.op (M.op x X0) X0) x X2
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq41 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq36 X0 (M.op X0 X0)
       grind)
    | exact superpose eq36 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq36 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq60 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq30
  have eq82 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) (τ X1)) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq83 x y
       grind)
    | exact superpose eq83 eq16
    | (have j1 := eq83 y y
       grind)
    | exact resolve eq16 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq83 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq121 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq271 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq122 (M.op X0 X0)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq122
    | (have j0 := eq122 (M.op X0 X0)
       grind)
    | exact resolve eq122 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq122 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq122
    | (have j0 := eq122 (τ X0)
       grind)
    | exact resolve eq122 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq122
  have eq276 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq271 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq278 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq275 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq275
    | (have j0 := eq275 X0
       grind)
    | exact resolve eq275 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq281 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq278 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq278
    | (have j0 := eq278 X0
       grind)
    | exact resolve eq278 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq288 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq281 (τ X0)
       have i₂ := eq45 X0 X0
       grind)
    | exact superpose eq45 eq281
    | (have j0 := eq281 (τ X0)
       grind)
    | exact resolve eq281 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq293 : ∀ X0 X1 : G, (σ (k X0 X0)) = (k (σ X0) (M.op X1 X1)) ∨ (M.op X1 X1) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 (σ X1)
       have i₂ := eq83 X1 X1
       grind)
    | exact superpose eq83 eq55
    | (have j1 := eq83 X0 X0
       grind)
    | exact resolve eq55 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq329 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X1) = (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (k (σ X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq293 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq343 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq36 (σ (M.op X0 X0)) x
       have i₂ := eq276 X0
       grind)
    | exact superpose eq276 eq36
    | exact resolve eq36 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ (M.op X0 X0)) X1
       have i₂ := eq276 X0
       grind)
    | exact superpose eq276 eq55
    | exact resolve eq55 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq963 : ∀ X0 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq288 (M.op X0 X0)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq288
    | (have j0 := eq288 (M.op X0 X0)
       grind)
    | exact resolve eq288 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq288
  have eq972 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq963 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq1004 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq36 (τ (M.op X0 X0)) x
       have i₂ := eq972 X0
       grind)
    | exact superpose eq972 eq36
    | exact resolve eq36 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972
  have eq1033 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq112
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq112
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq112 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq1034 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq1033
  have eq1044 : ∀ X0 X1 : G, (τ (τ (M.op X0 X0))) = (M.op X1 (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1004 (τ (M.op X0 X0)) X1
       have i₂ := eq1004 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq1004 eq1004
    | exact resolve eq1004 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1110 : ∀ X0 X1 : G, (τ (τ (τ (M.op X0 X0)))) = (M.op X1 (τ (τ (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1004 (τ (τ (M.op X0 X0))) X1
       have i₂ := eq1044 X0 (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq1044 eq1004
    | exact resolve eq1004 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2894 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    grind
  have eq2988 : ∀ X0 X1 : G, (σ (M.op X1 X1)) ≠ (k X0 (σ (M.op X1 X1))) ∨ (M.op X0 X0) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq345 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq3035 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq2894 X0 X1
       have j1 := eq2988 X1 X0
       grind)
    | (have r₁ := eq2894 X1 X0
       have r₂ := eq2988 X0 X1
       grind)
    | exact resolve eq2894 eq2988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2894 eq2988
  have eq3124 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3035 (τ (M.op X0 X0)) X1
       have i₂ := eq1004 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq1004 eq3035
    | exact resolve eq3035 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq3126 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ (τ (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3035 (τ (τ (M.op X0 X0))) X1
       have i₂ := eq1044 X0 (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq1044 eq3035
    | exact resolve eq3035 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq3127 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ (τ (τ (τ (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3035 (τ (τ (τ (M.op X0 X0)))) X1
       have i₂ := eq1110 X0 (τ (τ (τ (M.op X0 X0))))
       grind)
    | exact superpose eq1110 eq3035
    | exact resolve eq3035 eq1110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq3203 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq21 X0
       have i₂ := eq3035 (τ X0) X0
       grind)
    | exact superpose eq3035 eq21
    | exact resolve eq21 eq3035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq3035
  have eq3291 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3127 X0 X1
       have i₂ := eq11 (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq11 eq3127
    | exact resolve eq3127 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3127
  have eq3292 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3126 X0 X1
       have i₂ := eq11 (τ (M.op X0 X0))
       grind)
    | exact superpose eq11 eq3126
    | exact resolve eq3126 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3126
  have eq3294 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3124 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3124
    | exact resolve eq3124 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3124
  have eq3643 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3203 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3203
    | exact resolve eq3203 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3667 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq82 (τ X0) X0
       have i₂ := eq3203 X0
       grind)
    | exact superpose eq3203 eq82
    | (have j0 := eq82 (τ X0) X0
       grind)
    | exact resolve eq82 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq3676 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq3203 X0
       grind)
    | exact superpose eq3203 eq10
    | exact resolve eq10 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3203
  have eq3704 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq3667 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3667
  have eq3714 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq3704 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3704
    | (have j0 := eq3704 X0
       grind)
    | exact resolve eq3704 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3704
  have eq3731 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3714 X0
       have i₂ := eq3676 X0
       grind)
    | exact superpose eq3676 eq3714
    | (have j0 := eq3714 X0
       grind)
    | exact resolve eq3714 eq3676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3676 eq3714
  have eq3996 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3294 X1 (σ X0)
       have i₂ := eq3643 X0
       grind)
    | exact superpose eq3643 eq3294
    | exact resolve eq3294 eq3643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4432 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 (M.op X0 X0)
       have i₂ := eq3292 X1 (M.op X0 X0)
       grind)
    | exact superpose eq3292 eq36
    | exact resolve eq36 eq3292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4499 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq45 (M.op X1 X1) X0
       have i₂ := eq3292 X1 (τ X0)
       grind)
    | exact superpose eq3292 eq45
    | exact resolve eq45 eq3292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq3292
  have eq7352 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X2 (τ (τ (k X0 (M.op X1 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3291 X0 X2
       have i₂ := eq3294 X1 X0
       grind)
    | exact superpose eq3294 eq3291
    | exact resolve eq3291 eq3294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3291 eq3294
  have eq15882 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k (M.op X2 X2) (τ (τ (k X0 (M.op X1 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4432 X2 (τ X0)
       have i₂ := eq4499 X0 X1
       grind)
    | exact superpose eq4499 eq4432
    | exact resolve eq4432 eq4499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4432 eq4499
  have eq48292 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq276 y
       have i₂ := eq1034
       grind)
    | exact superpose eq1034 eq276
    | exact resolve eq276 eq1034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276 eq1034
  have eq48419 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq48292
  have eq48546 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq48419
       have i₂ := eq3643 y
       grind)
    | exact superpose eq3643 eq48419
    | exact resolve eq48419 eq3643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48419
  have eq48669 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq48546
       have i₂ := eq3643 x
       grind)
    | exact superpose eq3643 eq48546
    | exact resolve eq48546 eq3643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48546
  have eq50675 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq3731 (σ X0)
       grind)
    | exact superpose eq3731 eq60
    | (have j1 := eq3731 (σ X0)
       grind)
    | exact resolve eq60 eq3731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq3731
  have eq50824 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq50675 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq50675
    | (have j0 := eq50675 X0
       grind)
    | exact resolve eq50675 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50675
  have eq50855 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq50824 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq50824
    | (have j0 := eq50824 X0
       grind)
    | exact resolve eq50824 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50824
  have eq50868 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq50855 X0
       have i₂ := eq3643 X0
       grind)
    | exact superpose eq3643 eq50855
    | (have j0 := eq50855 X0
       grind)
    | exact resolve eq50855 eq3643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50855
  have eq67210 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k (σ X0) (M.op (σ X0) (σ X0))) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq329 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq67213 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) (M.op (σ X0) (σ X0))) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq67210 X0
       have i₂ := eq3643 X0
       grind)
    | exact superpose eq3643 eq67210
    | (have j0 := eq67210 X0
       grind)
    | exact resolve eq67210 eq3643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67210
  have eq67343 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (σ X0) ≠ (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq67213 X0
       have i₂ := eq3996 X0 (σ X0)
       grind)
    | exact superpose eq3996 eq67213
    | (have j0 := eq67213 X0
       grind)
    | exact resolve eq67213 eq3996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3996 eq67213
  have eq67344 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq67343 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67343
  have eq98575 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq50868 X0
       grind)
    | exact superpose eq50868 eq10
    | (have j1 := eq50868 X0
       grind)
    | exact resolve eq10 eq50868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50868
  have eq98691 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq98575 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq98575
    | (have j0 := eq98575 X0
       grind)
    | exact resolve eq98575 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98575
  have eq98847 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq98691 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq98691
    | exact resolve eq98691 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99024 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq98691 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98691
  have eq99090 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq98847 X0
       have i₂ := eq3643 X0
       grind)
    | exact superpose eq3643 eq98847
    | (have j0 := eq98847 X0
       grind)
    | exact resolve eq98847 eq3643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3643 eq98847
  have eq99140 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq99090 X0
       have j1 := eq67344 X0
       grind)
    | (have r₁ := eq99090 X0
       have r₂ := eq67344 X0
       grind)
    | exact resolve eq99090 eq67344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67344 eq99090
  have eq99857 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq99140 X0
       grind)
    | exact superpose eq99140 eq10
    | exact resolve eq10 eq99140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99140
  have eq99972 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq99857 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq99857
    | exact resolve eq99857 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99857
  have eq102217 : ∀ X0 X1 X2 : G, (k X0 (τ (τ (k X1 (M.op X2 X2))))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq99024 X0
       have i₂ := eq7352 X1 X2 X0
       grind)
    | exact superpose eq7352 eq99024
    | (have j0 := eq99024 X0
       grind)
    | exact resolve eq99024 eq7352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7352 eq99024
  have eq102379 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (k X0 (τ (τ (k X1 (M.op X2 X2))))) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq102217 X0 X1 X2
       have i₂ := eq99972 X0
       grind)
    | exact superpose eq99972 eq102217
    | (have j0 := eq102217 X0 X1 X2
       grind)
    | exact resolve eq102217 eq99972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99972 eq102217
  have eq871628 : (M.op x x) = (τ (σ y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq48669
       grind)
    | exact superpose eq48669 eq10
    | exact resolve eq10 eq48669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48669
  have eq871932 : y = (M.op x x) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq871628
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq871628
    | exact resolve eq871628 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871628
  have eq871933 : (σ y) = (σ (M.op y y)) ∨ y = (M.op x x) := by grind
  clear eq871932
  have eq872187 : (M.op y y) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq871933
       grind)
    | exact superpose eq871933 eq10
    | exact resolve eq10 eq871933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871933
  have eq872470 : y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq872187
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq872187
    | exact resolve eq872187 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872187
  have eq872964 : ∀ X0 X1 : G, y = (k y (τ (τ (k X0 (M.op X1 X1))))) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq15882 X0 X1 x
       have i₂ := eq872470
       grind)
    | exact superpose eq872470 eq15882
    | exact resolve eq15882 eq872470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15882 eq872470
  have eq873180 : y = (M.op y y) := by
    first
    | (have j1 := eq102379 y x x
       grind)
    | (have r₁ := eq872964 x x
       have r₂ := eq102379 y x x
       grind)
    | exact resolve eq872964 eq102379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102379 eq872964
  have eq874667 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq36 y x
       have i₂ := eq873180
       grind)
    | exact superpose eq873180 eq36
    | exact resolve eq36 eq873180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq874692 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq343 y x
       have i₂ := eq873180
       grind)
    | exact superpose eq873180 eq343
    | exact resolve eq343 eq873180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq873180
  have eq881070 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq874692 (σ x)
       grind)
    | exact superpose eq874692 eq16
    | exact resolve eq16 eq874692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874692
  have eq881107 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq881070
       have i₂ := eq874667 x
       grind)
    | exact superpose eq874667 eq881070
    | exact resolve eq881070 eq874667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874667 eq881070
  have eq881108 : False := by grind
  exact eq881108

/-- `Equation3545`: `x ◇ y = y ◇ ((x ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pyx_y_pyx_Equation3545 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3545 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3545.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq25 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) X1) = (M.op X1 (M.op X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq9 X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) X1) = (M.op X1 (M.op X0 (M.op X0 (M.op (M.op X0 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X1
       have i₂ := eq9 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq28 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) X1) = (M.op X1 (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 X1
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq26
    | exact resolve eq26 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq35 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq72 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq76 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq14 (M.op X0 (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq80 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq78 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq78 (k X0 X1) (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq78 (M.op X1 X0) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq78 (M.op X0 (k X1 X1)) X1
       have r₂ := eq12 X0 (k X1 X1)
       grind)
    | exact resolve eq78 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq82 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq76 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq76 X0 X0 X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq76 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq76 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq83 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq79 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq79 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq101 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq83 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq83
    | exact resolve eq83 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq123 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq28 X0 X1
       have i₂ := eq14 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X1 X1) X1)) = (M.op (M.op X0 (M.op X0 X0)) (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op (M.op X1 X1) X1)
       have i₂ := eq28 X1 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq28 eq28
    | exact resolve eq28 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) X1) = (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 (M.op X0 X0))) (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq28 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq28 eq9
    | exact resolve eq9 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) X1)) = (M.op (M.op (M.op X0 X0) X0) (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X1) X1)
       have i₂ := eq28 X1 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq28 eq9
    | exact resolve eq9 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X1))) ≠ X0 ∨ (M.op X0 (M.op (M.op X1 X1) X1)) = (k (M.op (M.op X1 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op (M.op X1 X1) X1) X0
       have i₂ := eq28 X1 X0
       grind)
    | exact superpose eq28 eq12
    | (have j0 := eq12 (M.op (M.op X1 X1) X1) X0
       grind)
    | exact resolve eq12 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X1) = (M.op X1 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq28 X0 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))
       grind)
    | exact superpose eq28 eq9
    | exact resolve eq9 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X1))) ≠ X0 ∨ (M.op X1 X0) = (k (M.op (M.op X1 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq131 X0 X1
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq131
    | (have j0 := eq131 X0 X1
       grind)
    | exact resolve eq131 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq136 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op (M.op X0 X0) X0) (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq129 X0 X1
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq129
    | exact resolve eq129 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq137 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) X1) = (M.op X1 (M.op X0 (M.op (M.op (M.op X0 X0) X0) (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq128 X0 X1
       have i₂ := eq9 X0 (M.op (M.op (M.op X0 X0) X0) (M.op X0 (M.op X0 X0)))
       grind)
    | exact superpose eq9 eq128
    | exact resolve eq128 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq140 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X0)) = (M.op (M.op X0 (M.op X0 X0)) (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq125 X0 X1
       have i₂ := eq9 X1 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq9 eq125
    | exact resolve eq125 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq142 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq123 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq123 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq123 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq148 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) X1) = (M.op X1 (M.op X0 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq137 X0 X1
       have i₂ := eq28 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq28 eq137
    | exact resolve eq137 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq151 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 (M.op X0 X0)) (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq140 X0 X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq140
    | exact resolve eq140 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq199 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 X0) ∨ (k X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq82 X1 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq82 X0 X1 X2
       have i₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact superpose eq14 eq82
    | (have j0 := eq82 X0 X1 X2
       have j1 := eq14 X0 X1
       grind)
    | exact resolve eq82 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) X1) = (M.op (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq82 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq82 eq28
    | (have j1 := eq82 X0 (M.op X0 X0) x
       grind)
    | exact resolve eq28 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X1)) = (M.op (M.op X2 X0) (M.op X1 (M.op X1 X1))) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X1 (M.op X2 X0)
       have i₂ := eq82 X2 X0 (M.op (M.op X1 X1) X1)
       grind)
    | exact superpose eq82 eq28
    | (have j1 := eq82 X2 X0 X2
       grind)
    | exact resolve eq28 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq216 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op X1 (M.op X1 X1))) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq215 X0 X1 X2
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq215
    | (have j0 := eq215 X0 X1 X2
       grind)
    | exact resolve eq215 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq221 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 X0) ∨ (k X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq199 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq199 (M.op X1 X0) X1 X0
       have r₂ := eq12 X0 (M.op X1 X0)
       grind)
    | (have r₁ := eq199 (M.op X0 (k X1 X1)) X1 X2
       have r₂ := eq12 X0 (k X1 X1)
       grind)
    | (have r₁ := eq199 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq199 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq619 : ∀ X0 X1 : G, (σ X1) = X0 ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X1 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | (have i₁ := eq72 X0 X1
       have i₂ := eq14 (M.op (σ X1) (σ X0)) X1
       grind)
    | exact superpose eq14 eq72
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq672 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq72 X0 X1
       grind)
    | exact superpose eq72 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq72 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq72 X1 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq72 X0 X1
       grind)
    | exact resolve eq12 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq677 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq672 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq691 : ∀ X0 X1 : G, (σ X1) = X0 ∨ (σ (k X1 X1)) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq619 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq696 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq677 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq677
    | (have j0 := eq677 X0 X1
       grind)
    | exact resolve eq677 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq697 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq696 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq714 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq691 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq691 (M.op X0 (σ X1)) X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq691 (M.op X0 (σ (k X1 X1))) X1
       have r₂ := eq12 X0 (σ (k X1 X1))
       grind)
    | (have r₁ := eq691 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq691 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq993 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X0 X0)) (M.op X1 (M.op X1 X1))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq136 X0 X1
       have i₂ := eq142 X0 X0 X0
       grind)
    | (have i₁ := eq136 (M.op X1 X0) X1
       have i₂ := eq142 X0 X1 (M.op (M.op X1 X0) (M.op X1 X0))
       grind)
    | exact superpose eq142 eq136
    | (have j1 := eq142 X0 X0 x
       grind)
    | exact resolve eq136 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq1053 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq993 X0 X1
       have i₂ := eq151 X0 X1
       grind)
    | exact superpose eq151 eq993
    | (have j0 := eq993 X0 X1
       grind)
    | exact resolve eq993 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993
  have eq1118 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq1053 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq1053 X0 X1
       grind)
    | exact superpose eq1053 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq1053 X0 X1
       grind)
    | exact resolve eq12 eq1053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053
  have eq1242 : ∀ X0 X1 : G, (M.op X0 X0) = (σ X1) ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq697 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq697
    | exact resolve eq697 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq1347 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1242 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq1242
    | (have j0 := eq1242 X0 X1
       grind)
    | exact resolve eq1242 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242
  have eq1648 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X2 ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X2 X0) = X0 ∨ (k X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X0
       have i₂ := eq221 X1 X0 X0
       grind)
    | (have i₁ := eq14 X0 X0
       have i₂ := eq221 X0 X1 X0
       grind)
    | exact superpose eq221 eq14
    | (have j0 := eq14 X2 X0
       have j1 := eq221 X1 X0 X2
       grind)
    | exact resolve eq14 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq1831 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X2 ∨ (k X2 X0) = (M.op X0 X2) ∨ (k X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1648 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq1648 X0 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq1648 X0 X1 (M.op X0 (M.op X0 X1))
       have r₂ := eq12 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq1648 X1 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1648 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1648
  have eq1906 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq714 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq714
    | (have j0 := eq714 X1 (τ X0)
       grind)
    | exact resolve eq714 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq1986 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1906 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq1906
    | (have j0 := eq1906 X0 X1
       grind)
    | exact resolve eq1906 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1906
  have eq1995 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1986 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1986
    | (have j0 := eq1986 X0 X1
       grind)
    | exact resolve eq1986 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1986
  have eq2001 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1995 X0 X1
       have j1 := eq80 X1 X0
       grind)
    | (have r₁ := eq1995 X0 X1
       have r₂ := eq80 (k X0 X0) X1
       grind)
    | (have r₁ := eq1995 X0 X0
       have r₂ := eq80 X0 (k X0 X0)
       grind)
    | (have r₁ := eq1995 X0 X1
       have r₂ := eq80 (M.op X0 X1) (k X1 X0)
       grind)
    | exact resolve eq1995 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq1995
  have eq2053 : ∀ X0 X1 : G, (τ X0) = (k X1 (τ (σ X1))) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (σ X1)
       have i₂ := eq2001 (σ X1) X0
       grind)
    | (have i₁ := eq35 X0 X1
       have i₂ := eq2001 X0 (k (σ X0) X1)
       grind)
    | exact superpose eq2001 eq35
    | (have j1 := eq2001 (σ X1) X0
       grind)
    | exact resolve eq35 eq2001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq2103 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2053 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2053
    | (have j0 := eq2053 X0 X1
       grind)
    | exact resolve eq2053 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2053
  have eq2435 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1347 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1347
    | exact resolve eq1347 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1347
  have eq2629 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) ∨ (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) ∨ (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  clear eq216
  have eq2667 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) ∨ (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq2629 X0
       have j1 := eq110 (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))
       grind)
    | (have r₁ := eq2629 X0
       have r₂ := eq110 (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq2629 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq2629
  have eq6072 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq2103 (σ X1) X0
       grind)
    | exact superpose eq2103 eq15
    | (have j1 := eq2103 (σ X1) X0
       grind)
    | exact resolve eq15 eq2103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2103
  have eq6092 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6072 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq6072
    | (have j0 := eq6072 X0 X1
       grind)
    | exact resolve eq6072 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6072
  have eq10606 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6092 x y
       grind)
    | exact superpose eq6092 eq16
    | (have j1 := eq6092 x y
       grind)
    | exact resolve eq16 eq6092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11096 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq10606
       have i₂ := eq2001 x y
       grind)
    | exact superpose eq2001 eq10606
    | (have j1 := eq2001 x y
       grind)
    | exact resolve eq10606 eq2001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2001 eq10606
  have eq11108 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x x) := by grind
  clear eq11096
  have eq11109 : y = (k x x) := by grind
  clear eq11108
  have eq187947 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1831 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1831
  have eq187999 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq187947 X0 X1
       have j1 := eq1118 X0 X0
       grind)
    | (have r₁ := eq187947 X1 (k X1 X1)
       have r₂ := eq1118 X1 X1
       grind)
    | (have r₁ := eq187947 X0 (k X0 X0)
       have r₂ := eq1118 X0 X1
       grind)
    | (have r₁ := eq187947 X0 X1
       have r₂ := eq1118 X0 X1
       grind)
    | exact resolve eq187947 eq1118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118 eq187947
  have eq188131 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq187999 X0 X0
       have j1 := eq2435 (k X0 X0) X0
       grind)
    | (have r₁ := eq187999 X1 X0
       have r₂ := eq2435 X0 X1
       grind)
    | (have r₁ := eq187999 X0 (M.op X1 X1)
       have r₂ := eq2435 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq187999 X0 (k X0 X0)
       have r₂ := eq2435 X0 X0
       grind)
    | exact resolve eq187999 eq2435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2435 eq187999
  have eq188238 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq188131 X0 X0
       have i₂ := eq6092 X0 X1
       grind)
    | (have i₁ := eq188131 X0 X1
       have i₂ := eq6092 X0 (k X1 X0)
       grind)
    | exact superpose eq6092 eq188131
    | (have j1 := eq6092 X1 X0
       grind)
    | exact resolve eq188131 eq6092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6092
  have eq188313 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq188131 x x
       have i₂ := eq11109
       grind)
    | exact superpose eq11109 eq188131
    | exact resolve eq188131 eq11109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11109
  have eq188617 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq188131 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188131
  have eq188618 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq188617 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188617
  have eq188628 : y = (M.op x x) := by grind
  clear eq188313
  have eq188635 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq188238 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188238
  have eq191687 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op y x)) := by
    intro X0
    first
    | (have i₁ := eq9 x X0
       have i₂ := eq188628
       grind)
    | exact superpose eq188628 eq9
    | exact resolve eq9 eq188628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191689 : ∀ X0 : G, (M.op (M.op y x) X0) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq28 x x
       have i₂ := eq188628
       grind)
    | exact superpose eq188628 eq28
    | exact resolve eq28 eq188628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191696 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op X0 (M.op (M.op y x) (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq134 x x
       have i₂ := eq188628
       grind)
    | exact superpose eq188628 eq134
    | exact resolve eq134 eq188628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq191697 : ∀ X0 : G, (M.op X0 (M.op x y)) ≠ X0 ∨ (M.op x X0) = (k (M.op y x) X0) := by
    intro X0
    first
    | (have i₁ := eq135 X0 x
       have i₂ := eq188628
       grind)
    | exact superpose eq188628 eq135
    | exact resolve eq135 eq188628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq191703 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq151 x X0
       have i₂ := eq188628
       grind)
    | exact superpose eq188628 eq151
    | exact resolve eq151 eq188628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq191710 : ∀ X0 : G, (M.op (M.op y x) X0) = (M.op y X0) ∨ (k x y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq205 x x
       have i₂ := eq188628
       grind)
    | exact superpose eq188628 eq205
    | exact resolve eq205 eq188628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq195721 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq188618 (σ X0)
       grind)
    | exact superpose eq188618 eq15
    | exact resolve eq15 eq188618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195777 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq195721 X0
       have i₂ := eq188618 X0
       grind)
    | exact superpose eq188618 eq195721
    | exact resolve eq195721 eq188618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195721
  have eq207475 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq195777 X0
       grind)
    | exact superpose eq195777 eq9
    | exact resolve eq9 eq195777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210922 : (M.op x (M.op y x)) = (M.op (M.op y x) (M.op x y)) := by
    first
    | (have i₁ := eq191687 (M.op y x)
       have i₂ := eq191689 (M.op y x)
       grind)
    | exact superpose eq191689 eq191687
    | exact resolve eq191687 eq191689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211195 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op y x)) := by
    first
    | (have i₁ := eq210922
       have i₂ := eq191689 (M.op x y)
       grind)
    | exact superpose eq191689 eq210922
    | exact resolve eq210922 eq191689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210922
  have eq211441 : (M.op x x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq211195
       have i₂ := eq191687 x
       grind)
    | exact superpose eq191687 eq211195
    | exact resolve eq211195 eq191687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211195
  have eq211599 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq211441
       have i₂ := eq188628
       grind)
    | exact superpose eq188628 eq211441
    | exact resolve eq211441 eq188628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211441
  have eq231194 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (M.op (σ y) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq207475 x X0
       have i₂ := eq188628
       grind)
    | exact superpose eq188628 eq207475
    | exact resolve eq207475 eq188628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207475
  have eq235491 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (M.op (σ y) (σ x))) (M.op (σ y) (σ x))) X0) = (M.op X0 (M.op (M.op (σ y) (σ x)) (M.op (M.op (M.op (σ y) (σ x)) (M.op (σ x) (M.op (σ y) (σ x)))) (M.op (M.op (σ y) (σ x)) (M.op (σ x) (M.op (σ y) (σ x))))))) := by
    intro X0
    first
    | (have i₁ := eq148 (M.op (σ y) (σ x)) x
       have i₂ := eq231194 (M.op (σ y) (σ x))
       grind)
    | exact superpose eq231194 eq148
    | exact resolve eq148 eq231194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq235704 : ∀ X0 : G, (M.op (M.op (σ y) (σ x)) X0) = (M.op X0 (M.op (σ x) (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))))) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op (σ y) (σ x)) X0
       have i₂ := eq231194 (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x)))
       grind)
    | exact superpose eq231194 eq9
    | exact resolve eq9 eq231194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235705 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ x)) (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))))) = (M.op (M.op (σ x) (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x)))) X0) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op (σ y) (σ x)) X0
       have i₂ := eq231194 (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x)))
       grind)
    | exact superpose eq231194 eq28
    | exact resolve eq28 eq231194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq235878 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ x)) (M.op (σ x) (M.op (σ y) (σ x))))) = (M.op (M.op (σ x) (M.op (σ x) (M.op (σ y) (σ x)))) X0) := by
    intro X0
    first
    | (have i₁ := eq235705 X0
       have i₂ := eq231194 (M.op (σ y) (σ x))
       grind)
    | exact superpose eq231194 eq235705
    | exact resolve eq235705 eq231194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235705
  have eq235879 : ∀ X0 : G, (M.op (M.op (σ y) (σ x)) X0) = (M.op X0 (M.op (σ x) (M.op (σ x) (M.op (σ y) (σ x))))) := by
    intro X0
    first
    | (have i₁ := eq235704 X0
       have i₂ := eq231194 (M.op (σ y) (σ x))
       grind)
    | exact superpose eq231194 eq235704
    | exact resolve eq235704 eq231194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235704
  have eq236019 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ y) (σ x))) X0) = (M.op X0 (M.op (M.op (σ y) (σ x)) (M.op (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x)))))) := by
    intro X0
    first
    | (have i₁ := eq235491 X0
       have i₂ := eq231194 (σ x)
       grind)
    | exact superpose eq231194 eq235491
    | exact resolve eq235491 eq231194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235491
  have eq236116 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ x))) X0) = (M.op X0 (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq235878 X0
       have i₂ := eq231194 (σ x)
       grind)
    | exact superpose eq231194 eq235878
    | exact resolve eq235878 eq231194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235878
  have eq236117 : ∀ X0 : G, (M.op (M.op (σ y) (σ x)) X0) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq235879 X0
       have i₂ := eq231194 (σ x)
       grind)
    | exact superpose eq231194 eq235879
    | exact resolve eq235879 eq231194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235879
  have eq236249 : ∀ X0 : G, (M.op (M.op (σ (M.op x x)) (M.op (σ y) (σ x))) X0) = (M.op X0 (M.op (M.op (σ y) (σ x)) (M.op (M.op (M.op (σ y) (σ x)) (σ (M.op x x))) (M.op (M.op (σ y) (σ x)) (σ (M.op x x)))))) := by
    intro X0
    first
    | (have i₁ := eq236019 X0
       have i₂ := eq195777 x
       grind)
    | exact superpose eq195777 eq236019
    | exact resolve eq236019 eq195777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236019
  have eq236323 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ x)) (σ (M.op x x)))) = (M.op (M.op (σ x) (σ (M.op x x))) X0) := by
    intro X0
    first
    | (have i₁ := eq236116 X0
       have i₂ := eq195777 x
       grind)
    | exact superpose eq195777 eq236116
    | exact resolve eq236116 eq195777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236116
  have eq236324 : ∀ X0 : G, (M.op (M.op (σ y) (σ x)) X0) = (M.op X0 (M.op (σ x) (σ (M.op x x)))) := by
    intro X0
    first
    | (have i₁ := eq236117 X0
       have i₂ := eq195777 x
       grind)
    | exact superpose eq195777 eq236117
    | exact resolve eq236117 eq195777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236117
  have eq236450 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ y) (σ x))) X0) = (M.op X0 (M.op (M.op (σ y) (σ x)) (M.op (M.op (M.op (σ y) (σ x)) (σ y)) (M.op (M.op (σ y) (σ x)) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq236249 X0
       have i₂ := eq188628
       grind)
    | exact superpose eq188628 eq236249
    | exact resolve eq236249 eq188628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236249
  have eq236515 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op X0 (M.op (M.op (σ y) (σ x)) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq236323 X0
       have i₂ := eq188628
       grind)
    | exact superpose eq188628 eq236323
    | exact resolve eq236323 eq188628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236323
  have eq236516 : ∀ X0 : G, (M.op (M.op (σ y) (σ x)) X0) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq236324 X0
       have i₂ := eq188628
       grind)
    | exact superpose eq188628 eq236324
    | exact resolve eq236324 eq188628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236324
  have eq236612 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op X0 (M.op (M.op (σ y) (σ x)) (M.op (M.op (M.op (σ y) (σ x)) (σ y)) (M.op (M.op (σ y) (σ x)) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq236450 X0
       have i₂ := eq231194 (σ y)
       grind)
    | exact superpose eq231194 eq236450
    | exact resolve eq236450 eq231194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236450
  have eq236737 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op X0 (M.op (M.op (σ y) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (σ x)) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq236612 X0
       have i₂ := eq236515 (M.op (M.op (σ y) (σ x)) (σ y))
       grind)
    | exact superpose eq236515 eq236612
    | exact resolve eq236612 eq236515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236612
  have eq236840 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op X0 (M.op (M.op (σ y) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq236737 X0
       have i₂ := eq236515 (M.op (σ x) (σ y))
       grind)
    | exact superpose eq236515 eq236737
    | exact resolve eq236737 eq236515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236515 eq236737
  have eq394766 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) ≠ X0 ∨ (M.op X0 (M.op (σ y) (σ x))) = (k (M.op (σ y) (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op (σ y) (σ x)) X0
       have i₂ := eq236516 X0
       grind)
    | exact superpose eq236516 eq12
    | (have j0 := eq12 (M.op (σ y) (σ x)) X0
       grind)
    | exact resolve eq12 eq236516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq394880 : (M.op (σ x) (M.op (σ y) (σ x))) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq231194 (M.op (σ y) (σ x))
       have i₂ := eq236516 (M.op (σ y) (σ x))
       grind)
    | exact superpose eq236516 eq231194
    | exact resolve eq231194 eq236516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq395252 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq394880
       have i₂ := eq236516 (M.op (σ x) (σ y))
       grind)
    | exact superpose eq236516 eq394880
    | exact resolve eq394880 eq236516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394880
  have eq395324 : ∀ X0 : G, (M.op (σ x) X0) = (k (M.op (σ y) (σ x)) X0) ∨ (M.op X0 (M.op (σ x) (σ y))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq394766 X0
       have i₂ := eq231194 X0
       grind)
    | exact superpose eq231194 eq394766
    | (have j0 := eq394766 X0
       grind)
    | exact resolve eq394766 eq231194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394766
  have eq395634 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq395252
       have i₂ := eq231194 (σ x)
       grind)
    | exact superpose eq231194 eq395252
    | exact resolve eq395252 eq231194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395252
  have eq395850 : (σ (M.op x x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq395634
       have i₂ := eq195777 x
       grind)
    | exact superpose eq195777 eq395634
    | exact resolve eq395634 eq195777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395634
  have eq396013 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq395850
       have i₂ := eq188628
       grind)
    | exact superpose eq188628 eq395850
    | exact resolve eq395850 eq188628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395850
  have eq656832 : (M.op x (M.op y x)) = (M.op (M.op x y) (M.op (M.op y x) (M.op y (M.op y x)))) ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq191703 (M.op y x)
       have i₂ := eq191710 (M.op y x)
       grind)
    | exact superpose eq191710 eq191703
    | exact resolve eq191703 eq191710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191703 eq191710
  have eq657493 : (M.op x (M.op y x)) = (M.op (M.op x y) (M.op (M.op y x) (M.op x y))) ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq656832
       have i₂ := eq191687 y
       grind)
    | exact superpose eq191687 eq656832
    | exact resolve eq656832 eq191687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656832
  have eq657888 : (M.op x (M.op y x)) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq657493
       have i₂ := eq191689 (M.op x y)
       grind)
    | exact superpose eq191689 eq657493
    | exact resolve eq657493 eq191689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657493
  have eq658181 : (M.op (M.op x y) y) = (M.op x (M.op y x)) ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq657888
       have i₂ := eq211599
       grind)
    | exact superpose eq211599 eq657888
    | exact resolve eq657888 eq211599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657888
  have eq658416 : (M.op x x) = (M.op (M.op x y) y) ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq658181
       have i₂ := eq191687 x
       grind)
    | exact superpose eq191687 eq658181
    | exact resolve eq658181 eq191687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658181
  have eq658567 : y = (M.op (M.op x y) y) ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq658416
       have i₂ := eq188628
       grind)
    | exact superpose eq188628 eq658416
    | exact resolve eq658416 eq188628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658416
  have eq670843 : y = (M.op y (M.op y x)) ∨ (k x y) = (M.op y x) ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq142 x y y
       have i₂ := eq658567
       grind)
    | exact superpose eq658567 eq142
    | (have j0 := eq142 x y x
       grind)
    | exact resolve eq142 eq658567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq658567
  have eq670961 : y = (M.op y (M.op y x)) ∨ (k x y) = (M.op y x) := by grind
  clear eq670843
  have eq671001 : y = (M.op x y) ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq670961
       have i₂ := eq191687 y
       grind)
    | exact superpose eq191687 eq670961
    | exact resolve eq670961 eq191687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670961
  have eq671015 : (k x y) = (M.op y x) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq671001
       have r₂ := eq12 x y
       grind)
    | exact resolve eq671001 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671001
  have eq988130 : (M.op (M.op (σ y) (σ x)) (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y)))) = (k (M.op (M.op (σ y) (σ x)) (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y)))) (M.op (M.op (σ y) (σ x)) (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))))) ∨ (M.op (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) (M.op (σ y) (σ x))) = (k (M.op (σ y) (σ x)) (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq2667 (M.op (σ y) (σ x))
       have i₂ := eq236516 (M.op (σ y) (σ x))
       grind)
    | exact superpose eq236516 eq2667
    | exact resolve eq2667 eq236516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq988147 : (M.op (M.op y x) (M.op (M.op y x) (M.op x y))) = (k (M.op (M.op y x) (M.op (M.op y x) (M.op x y))) (M.op (M.op y x) (M.op (M.op y x) (M.op x y)))) ∨ (M.op (M.op (M.op y x) (M.op x y)) (M.op y x)) = (k (M.op y x) (M.op (M.op y x) (M.op x y))) := by
    first
    | (have i₁ := eq2667 (M.op y x)
       have i₂ := eq191689 (M.op y x)
       grind)
    | exact superpose eq191689 eq2667
    | exact resolve eq2667 eq191689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2667
  have eq988735 : (M.op (M.op y x) (M.op (M.op y x) (M.op x y))) = (M.op (M.op (M.op y x) (M.op (M.op y x) (M.op x y))) (M.op (M.op y x) (M.op (M.op y x) (M.op x y)))) ∨ (M.op (M.op (M.op y x) (M.op x y)) (M.op y x)) = (k (M.op y x) (M.op (M.op y x) (M.op x y))) := by
    first
    | (have i₁ := eq988147
       have i₂ := eq188618 (M.op (M.op y x) (M.op (M.op y x) (M.op x y)))
       grind)
    | exact superpose eq188618 eq988147
    | exact resolve eq988147 eq188618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988147
  have eq988750 : (M.op (M.op (σ y) (σ x)) (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op (σ y) (σ x)) (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y)))) (M.op (M.op (σ y) (σ x)) (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))))) ∨ (M.op (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) (M.op (σ y) (σ x))) = (k (M.op (σ y) (σ x)) (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq988130
       have i₂ := eq188618 (M.op (M.op (σ y) (σ x)) (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))))
       grind)
    | exact superpose eq188618 eq988130
    | exact resolve eq988130 eq188618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188618 eq988130
  have eq988916 : (M.op (M.op y x) (M.op (M.op x y) (M.op x y))) = (M.op (M.op (M.op y x) (M.op (M.op x y) (M.op x y))) (M.op (M.op y x) (M.op (M.op x y) (M.op x y)))) ∨ (M.op (M.op (M.op y x) (M.op x y)) (M.op y x)) = (k (M.op y x) (M.op (M.op y x) (M.op x y))) := by
    first
    | (have i₁ := eq988735
       have i₂ := eq191689 (M.op x y)
       grind)
    | exact superpose eq191689 eq988735
    | exact resolve eq988735 eq191689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988735
  have eq988922 : (M.op (M.op (σ y) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op (σ y) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ y) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) (M.op (σ y) (σ x))) = (k (M.op (σ y) (σ x)) (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq988750
       have i₂ := eq236516 (M.op (σ x) (σ y))
       grind)
    | exact superpose eq236516 eq988750
    | exact resolve eq988750 eq236516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988750
  have eq988989 : (M.op (M.op y x) (M.op (M.op x y) (M.op x y))) = (M.op (M.op x y) (M.op (M.op y x) (M.op (M.op x y) (M.op x y)))) ∨ (M.op (M.op (M.op y x) (M.op x y)) (M.op y x)) = (k (M.op y x) (M.op (M.op y x) (M.op x y))) := by
    first
    | (have i₁ := eq988916
       have i₂ := eq191696 (M.op (M.op y x) (M.op (M.op x y) (M.op x y)))
       grind)
    | exact superpose eq191696 eq988916
    | exact resolve eq988916 eq191696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988916
  have eq988995 : (M.op (M.op (σ y) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) (M.op (σ y) (σ x))) = (k (M.op (σ y) (σ x)) (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq988922
       have i₂ := eq236840 (M.op (M.op (σ y) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))
       grind)
    | exact superpose eq236840 eq988922
    | exact resolve eq988922 eq236840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988922
  have eq989048 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op y x) (M.op (M.op x y) (M.op x y))) ∨ (M.op (M.op (M.op y x) (M.op x y)) (M.op y x)) = (k (M.op y x) (M.op (M.op y x) (M.op x y))) := by
    first
    | (have i₁ := eq988989
       have i₂ := eq191696 (M.op x y)
       grind)
    | exact superpose eq191696 eq988989
    | exact resolve eq988989 eq191696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191696 eq988989
  have eq989054 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) (M.op (σ y) (σ x))) = (k (M.op (σ y) (σ x)) (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq988995
       have i₂ := eq236840 (M.op (σ x) (σ y))
       grind)
    | exact superpose eq236840 eq988995
    | exact resolve eq988995 eq236840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236840 eq988995
  have eq989093 : y = (M.op (M.op y x) y) ∨ (M.op (M.op (M.op y x) (M.op x y)) (M.op y x)) = (k (M.op y x) (M.op (M.op y x) (M.op x y))) := by
    first
    | (have i₁ := eq989048
       have i₂ := eq211599
       grind)
    | exact superpose eq211599 eq989048
    | exact resolve eq989048 eq211599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989048
  have eq989099 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (M.op (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) (M.op (σ y) (σ x))) = (k (M.op (σ y) (σ x)) (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq989054
       have i₂ := eq396013
       grind)
    | exact superpose eq396013 eq989054
    | exact resolve eq989054 eq396013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989054
  have eq989133 : y = (M.op y (M.op x y)) ∨ (M.op (M.op (M.op y x) (M.op x y)) (M.op y x)) = (k (M.op y x) (M.op (M.op y x) (M.op x y))) := by
    first
    | (have i₁ := eq989093
       have i₂ := eq191689 y
       grind)
    | exact superpose eq191689 eq989093
    | exact resolve eq989093 eq191689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989093
  have eq989139 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) (M.op (σ y) (σ x))) = (k (M.op (σ y) (σ x)) (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq989099
       have i₂ := eq236516 (σ y)
       grind)
    | exact superpose eq236516 eq989099
    | exact resolve eq989099 eq236516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989099
  have eq989167 : (M.op (M.op (M.op x y) (M.op x y)) (M.op y x)) = (k (M.op y x) (M.op (M.op x y) (M.op x y))) ∨ y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq989133
       have i₂ := eq191689 (M.op x y)
       grind)
    | exact superpose eq191689 eq989133
    | exact resolve eq989133 eq191689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191689 eq989133
  have eq989173 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ y) (σ x))) = (k (M.op (σ y) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq989139
       have i₂ := eq236516 (M.op (σ x) (σ y))
       grind)
    | exact superpose eq236516 eq989139
    | exact resolve eq989139 eq236516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236516 eq989139
  have eq989199 : (k (M.op y x) y) = (M.op y (M.op y x)) ∨ y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq989167
       have i₂ := eq211599
       grind)
    | exact superpose eq211599 eq989167
    | exact resolve eq989167 eq211599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211599 eq989167
  have eq989205 : (M.op (σ y) (M.op (σ y) (σ x))) = (k (M.op (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq989173
       have i₂ := eq396013
       grind)
    | exact superpose eq396013 eq989173
    | exact resolve eq989173 eq396013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396013 eq989173
  have eq989231 : (M.op x y) = (k (M.op y x) y) ∨ y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq989199
       have i₂ := eq191687 y
       grind)
    | exact superpose eq191687 eq989199
    | exact resolve eq989199 eq191687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989199
  have eq989237 : (M.op (σ x) (σ y)) = (k (M.op (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq989205
       have i₂ := eq231194 (σ y)
       grind)
    | exact superpose eq231194 eq989205
    | exact resolve eq989205 eq231194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231194 eq989205
  have eq989261 : (M.op x y) = (k (M.op y x) y) := by
    first
    | (have j1 := eq191697 y
       grind)
    | (have r₁ := eq989231
       have r₂ := eq191697 y
       grind)
    | exact resolve eq989231 eq191697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191697 eq989231
  have eq989267 : (M.op (σ x) (σ y)) = (k (M.op (σ y) (σ x)) (σ y)) := by
    first
    | (have j1 := eq395324 (σ y)
       grind)
    | (have r₁ := eq989237
       have r₂ := eq395324 (σ y)
       grind)
    | exact resolve eq989237 eq395324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395324 eq989237
  have eq1003416 : (M.op (σ x) (σ y)) = (k (σ (k x y)) (σ y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq989267
       have i₂ := eq101 x y
       grind)
    | exact superpose eq101 eq989267
    | (have j1 := eq101 x y
       grind)
    | exact resolve eq989267 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq1003439 : (M.op (σ x) (σ y)) = (k (σ (k x y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq989267
       have i₂ := eq188635 x y
       grind)
    | exact superpose eq188635 eq989267
    | (have j1 := eq188635 x y
       grind)
    | exact resolve eq989267 eq188635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188635 eq989267
  have eq1003662 : (M.op (σ x) (σ y)) = (σ (k (k x y) y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1003439
       have i₂ := eq15 (k x y) y
       grind)
    | exact superpose eq15 eq1003439
    | exact resolve eq1003439 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003439
  have eq1003679 : (M.op (σ x) (σ y)) = (σ (k (k x y) y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq1003416
       have i₂ := eq15 (k x y) y
       grind)
    | exact superpose eq15 eq1003416
    | exact resolve eq1003416 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003416
  have eq1003708 : (M.op (σ x) (σ y)) = (σ (k (M.op y x) y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1003662
       have i₂ := eq671015
       grind)
    | exact superpose eq671015 eq1003662
    | exact resolve eq1003662 eq671015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003662
  have eq1003725 : (M.op (σ x) (σ y)) = (σ (k (M.op y x) y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq1003679
       have i₂ := eq671015
       grind)
    | exact superpose eq671015 eq1003679
    | exact resolve eq1003679 eq671015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003679
  have eq1003749 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1003708
       have i₂ := eq989261
       grind)
    | exact superpose eq989261 eq1003708
    | exact resolve eq1003708 eq989261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003708
  have eq1003766 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq1003725
       have i₂ := eq989261
       grind)
    | exact superpose eq989261 eq1003725
    | exact resolve eq1003725 eq989261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989261 eq1003725
  have eq1003783 : x = (M.op y y) := by
    first
    | (have r₁ := eq1003749
       have r₂ := eq16
       grind)
    | exact resolve eq1003749 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003749
  have eq1003800 : (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq1003766
       have r₂ := eq16
       grind)
    | exact resolve eq1003766 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003766
  have eq1003819 : (σ y) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq1003800
       have i₂ := eq671015
       grind)
    | exact superpose eq671015 eq1003800
    | exact resolve eq1003800 eq671015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671015 eq1003800
  have eq1015650 : (M.op (σ y) (σ y)) = (σ (M.op (M.op y x) (M.op y x))) := by
    first
    | (have i₁ := eq195777 (M.op y x)
       have i₂ := eq1003819
       grind)
    | exact superpose eq1003819 eq195777
    | exact resolve eq195777 eq1003819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003819
  have eq1015666 : (M.op (σ y) (σ y)) = (σ (M.op x (M.op y x))) := by
    first
    | (have i₁ := eq1015650
       have i₂ := eq191687 (M.op y x)
       grind)
    | exact superpose eq191687 eq1015650
    | exact resolve eq1015650 eq191687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015650
  have eq1016034 : (M.op (σ y) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1015666
       have i₂ := eq191687 x
       grind)
    | exact superpose eq191687 eq1015666
    | exact resolve eq1015666 eq191687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191687 eq1015666
  have eq1016298 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1016034
       have i₂ := eq188628
       grind)
    | exact superpose eq188628 eq1016034
    | exact resolve eq1016034 eq188628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016034
  have eq1016478 : (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1016298
       have i₂ := eq195777 y
       grind)
    | exact superpose eq195777 eq1016298
    | exact resolve eq1016298 eq195777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016298
  have eq1016637 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1016478
       have i₂ := eq1003783
       grind)
    | exact superpose eq1003783 eq1016478
    | exact resolve eq1016478 eq1003783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003783 eq1016478
  have eq1025077 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1016637
       grind)
    | exact superpose eq1016637 eq16
    | exact resolve eq16 eq1016637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1025094 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1016637
       grind)
    | exact superpose eq1016637 eq10
    | exact resolve eq10 eq1016637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1025643 : x = y := by
    first
    | (have i₁ := eq1025094
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1025094
    | exact resolve eq1025094 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025094
  have eq1025656 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1025077
       have i₂ := eq195777 x
       grind)
    | exact superpose eq195777 eq1025077
    | exact resolve eq1025077 eq195777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195777 eq1025077
  have eq1025812 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq1025656
       have i₂ := eq188628
       grind)
    | exact superpose eq188628 eq1025656
    | exact resolve eq1025656 eq188628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025656
  have eq1025929 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq1025812
       have i₂ := eq1016637
       grind)
    | exact superpose eq1016637 eq1025812
    | exact resolve eq1025812 eq1016637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025812
  have eq1026002 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1025929
       have i₂ := eq1025643
       grind)
    | exact superpose eq1025643 eq1025929
    | exact resolve eq1025929 eq1025643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025643 eq1025929
  have eq1026035 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq1026002
       have i₂ := eq188628
       grind)
    | exact superpose eq188628 eq1026002
    | exact resolve eq1026002 eq188628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188628 eq1026002
  have eq1026060 : False := by grind
  exact eq1026060

/-- `Equation3690`: `x ◇ x = (y ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyx_pyx_pxx_pyx_Equation3690 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3690 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3690.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq51 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq64 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq69 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq72 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq630 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq639 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq630 X0 X1
       have j1 := eq72 X0 X1
       grind)
    | (have r₁ := eq630 X0 X1
       have r₂ := eq72 X0 X1
       grind)
    | (have r₁ := eq630 X0 X0
       have r₂ := eq72 X0 X0
       grind)
    | exact resolve eq630 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq630
  have eq4727 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq639
  have eq4819 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq4727 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4727
  have eq6442 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq4819 (σ X1) (σ X0)
       grind)
    | exact superpose eq4819 eq15
    | exact resolve eq15 eq4819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6457 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6442 X0 X1
       have i₂ := eq4819 X1 X0
       grind)
    | exact superpose eq4819 eq6442
    | exact resolve eq6442 eq4819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4819 eq6442
  have eq6470 : False := by grind
  exact eq6470

/-- `Equation3866`: `x ◇ x = (x ◇ (x ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_x_pyx_pxy_Equation3866 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3866 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3866.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
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
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq174 : x ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq175 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (M.op x x) = (M.op (M.op x (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) = (M.op (M.op X0 X0) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 (M.op X0 (M.op X0 X1)) x X3
       have i₂ := eq16 X0 X1 (M.op (M.op X0 (M.op X0 X1)) x)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X3) := by
    intro X0 X3
    first
    | (have i₁ := eq179 X0 x X3
       have i₂ := eq16 X0 x (M.op X0 (M.op X0 x))
       grind)
    | exact superpose eq16 eq179
    | exact resolve eq179 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq201 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 x (M.op X0 X0)
       have r₂ := eq181 X0 x
       grind)
    | exact resolve eq13 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq201 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq690 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq692 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 (k X0 X1)) X2) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq694 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (k X0 (M.op X0 X1)) X2) ∨ (M.op X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq11 X0 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 (M.op X0 X1)
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 X1 : G, (k X0 X0) = (M.op (k X0 X0) X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq181 X1 x
       have i₂ := eq11 X1 X1
       grind)
    | exact superpose eq11 eq181
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq181 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq717 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq718 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq719 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq718 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq733 : ∀ X0 X1 : G, (k X0 X0) = (M.op (k X0 X0) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq695 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq1280 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq690
       grind)
    | exact superpose eq690 eq40
    | exact resolve eq40 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1281 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1280
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1280
    | exact resolve eq1280 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280
  have eq1283 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq1281
    | exact resolve eq1281 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281
  have eq1333 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1283 eq691
    | exact resolve eq691 eq1283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283
  have eq1340 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq1333
       have r₂ := eq27
       grind)
    | exact resolve eq1333 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1333
  have eq1347 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1340 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1340
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1340
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1340
       grind)
    | exact resolve eq13 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340
  have eq1348 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq1347
  have eq1361 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1348 eq152
    | exact resolve eq152 eq1348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq1348
  have eq1366 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq1361
    | exact resolve eq1361 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1361
  have eq1369 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq1366
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq1366
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq1366
       have r₂ := eq13 x y
       grind)
    | exact resolve eq1366 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1366
  have eq1373 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq690
       have i₂ := eq1369
       grind)
    | exact superpose eq1369 eq690
    | exact resolve eq690 eq1369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq1375 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1369
       grind)
    | exact superpose eq1369 eq40
    | exact resolve eq40 eq1369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1369
  have eq1376 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1373
  have eq1378 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1375
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1375
    | exact resolve eq1375 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375
  have eq1382 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1376
       grind)
    | exact superpose eq1376 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1376
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1376
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1376
       grind)
    | exact resolve eq12 eq1376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1376
  have eq1386 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1382
  have eq1387 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1386
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1386
    | exact resolve eq1386 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1386
  have eq1388 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1387
  have eq1390 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1388
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1388
    | exact resolve eq1388 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1388
  have eq1396 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1378 eq691
    | exact resolve eq691 eq1378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691 eq1378
  have eq1400 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1396
  have eq1409 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1390
       grind)
    | exact superpose eq1390 eq39
    | exact resolve eq39 eq1390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390
  have eq1410 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1409
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1409
    | exact resolve eq1409 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409
  have eq1412 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1410
    | exact resolve eq1410 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410
  have eq1415 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1400 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1400
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1400
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1400
       grind)
    | exact resolve eq12 eq1400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400
  have eq1419 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1415
  have eq1420 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1419
    | exact resolve eq1419 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1419
  have eq1421 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1420
  have eq1423 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1421
    | exact resolve eq1421 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1421
  have eq1425 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1412 eq1423
    | exact resolve eq1423 eq1412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412 eq1423
  have eq1426 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1425
       have r₂ := eq27
       grind)
    | exact resolve eq1425 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425
  have eq1428 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1426 eq175
    | (have r₁ := eq175
       have r₂ := eq1426
       grind)
    | exact resolve eq175 eq1426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq1429 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1426 eq27
    | exact resolve eq27 eq1426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1430 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1428
  have eq1433 : (τ (σ y)) = (k (τ (σ y)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1430 eq141
    | exact resolve eq141 eq1430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq1430
  have eq1434 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq1433
    | exact resolve eq1433 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1433
  have eq1437 : y = (k y x) := by
    first
    | (have r₁ := eq1434
       have r₂ := eq174
       grind)
    | exact resolve eq1434 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq1434
  have eq1443 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1437
       grind)
    | exact superpose eq1437 eq39
    | exact resolve eq39 eq1437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1444 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1443
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1443
    | exact resolve eq1443 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1443
  have eq1789 : y ≠ y ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq717 y x
       have i₂ := eq1437
       grind)
    | exact superpose eq1437 eq717
    | (have j0 := eq717 y x
       grind)
    | (have r₁ := eq717 y x
       have r₂ := eq1437
       grind)
    | exact resolve eq717 eq1437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1821 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1444 eq717
    | (have j0 := eq717 (σ y) (σ x)
       grind)
    | (have r₁ := eq717 (σ y) (σ x)
       have r₂ := eq1444
       grind)
    | exact resolve eq717 eq1444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq1826 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1821
  have eq1857 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq1789
  have eq1883 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1826
    | exact resolve eq1826 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1826
  have eq1888 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1857
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1857
    | exact resolve eq1857 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1857
  have eq2017 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1888
       grind)
    | exact superpose eq1888 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1888
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1888
       grind)
    | exact resolve eq12 eq1888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2021 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq2017
  have eq2022 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2021
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2021
    | exact resolve eq2021 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2021
  have eq2023 : x = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq2022
  have eq2024 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2023
       have i₂ := eq1437
       grind)
    | exact superpose eq1437 eq2023
    | exact resolve eq2023 eq1437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1437 eq2023
  have eq2025 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2024
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2024
    | exact resolve eq2024 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2024
  have eq2026 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2025
       grind)
    | exact superpose eq2025 eq18
    | exact resolve eq18 eq2025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2027 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2025
       grind)
    | exact superpose eq2025 eq24
    | exact resolve eq24 eq2025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2043 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1888
       have i₂ := eq2025
       grind)
    | exact superpose eq2025 eq1888
    | exact resolve eq1888 eq2025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1888 eq2025
  have eq2044 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq2043
  have eq2053 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2027
    | exact resolve eq2027 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2027
  have eq2070 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2053 eq1429
    | exact resolve eq1429 eq2053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429
  have eq2072 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq2070
  have eq2103 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1883 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1883
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1883
       grind)
    | exact resolve eq12 eq1883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2107 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2103
  have eq2108 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq2107
    | exact resolve eq2107 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2107
  have eq2109 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq2108
  have eq2110 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1444 eq2109
    | exact resolve eq2109 eq1444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1444 eq2109
  have eq2111 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq2110
    | exact resolve eq2110 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2110
  have eq2113 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2111 eq177
    | exact resolve eq177 eq2111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq2116 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq2117 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq2113
    | (have j0 := eq2113 X0
       grind)
    | exact resolve eq2113 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2113
  have eq2119 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2111 eq2117
    | exact resolve eq2117 eq2111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2111 eq2117
  have eq2166 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2026 eq176
    | exact resolve eq176 eq2026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq2026
  have eq2231 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2119 eq1883
    | exact resolve eq1883 eq2119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1883 eq2119
  have eq2283 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2231
  have eq2294 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2283 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq2283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2283
  have eq2339 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2294
  have eq2362 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2339
       have r₂ := eq2116
       grind)
    | exact resolve eq2339 eq2116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2339
  have eq2515 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2362 eq97
    | exact resolve eq97 eq2362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq2362
  have eq2525 : y = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq2515
    | exact resolve eq2515 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2515
  have eq2528 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1426 eq2525
    | exact resolve eq2525 eq1426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2525
  have eq2846 : ∀ X0 X1 : G, (k X1 (M.op (M.op x y) X0)) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq203 x X1
       have i₂ := eq2166 X0
       grind)
    | exact superpose eq2166 eq203
    | exact resolve eq203 eq2166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq2902 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2044 eq2846
    | exact resolve eq2846 eq2044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2044 eq2846
  have eq2921 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2902 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2902
  have eq2933 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2921 eq719
    | (have j0 := eq719 (M.op x y)
       grind)
    | (have r₁ := eq719 (M.op x y)
       have r₂ := eq2921 (M.op x y)
       grind)
    | exact resolve eq719 eq2921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719 eq2921
  have eq2947 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq2933
  have eq2970 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2947 eq181
    | exact resolve eq181 eq2947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2947
  have eq3130 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2970 eq2166
    | exact resolve eq2166 eq2970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2166 eq2970
  have eq3182 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq3130
  have eq3322 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq3182
       grind)
    | exact superpose eq3182 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq3182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3182
  have eq3367 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq3322
  have eq3510 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq3367
       grind)
    | exact superpose eq3367 eq39
    | exact resolve eq39 eq3367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq3367
  have eq3517 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3510
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3510
    | exact resolve eq3510 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3510
  have eq3519 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq3517
    | exact resolve eq3517 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3517
  have eq3521 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2053 eq3519
    | exact resolve eq3519 eq2053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2053 eq3519
  have eq4337 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3521 eq692
    | (have j0 := eq692 (σ x) (σ x) x
       grind)
    | exact resolve eq692 eq3521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq4420 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq4337 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4337
  have eq4436 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq4420
    | (have j0 := eq4420 X0
       grind)
    | exact resolve eq4420 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4420
  have eq4440 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1426 eq4436
    | exact resolve eq4436 eq1426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4436
  have eq12524 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4440 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq4440 X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq4440 X0
       grind)
    | exact resolve eq13 eq4440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12530 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4440 eq26
    | (have j1 := eq4440 (σ y)
       grind)
    | exact resolve eq26 eq4440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4440
  have eq12562 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1426 eq12530
    | exact resolve eq12530 eq1426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426 eq12530
  have eq12563 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq12562
  have eq12569 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq12524 X0
       have j1 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq12524 X0
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq12524 X0
       have r₂ := eq13 y x
       grind)
    | exact resolve eq12524 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12524
  have eq12581 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3521 eq12569
    | (have j0 := eq12569 X0
       grind)
    | exact resolve eq12569 eq3521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3521 eq12569
  have eq12583 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq12581 X0
       grind)
    | (have r₁ := eq12581 X0
       have r₂ := eq2072
       grind)
    | exact resolve eq12581 eq2072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2072 eq12581
  have eq12593 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12563 eq181
    | exact resolve eq181 eq12563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq12563
  have eq12666 : x = (M.op x y) := by
    first
    | (have r₁ := eq12593 x
       have r₂ := eq12583 x
       grind)
    | exact resolve eq12593 eq12583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12583 eq12593
  have eq12670 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq12666
       grind)
    | exact superpose eq12666 eq18
    | exact resolve eq18 eq12666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq12671 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq12666
       grind)
    | exact superpose eq12666 eq22
    | exact resolve eq22 eq12666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq12666
  have eq12686 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq12671 eq20
    | exact resolve eq20 eq12671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq12847 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (k (M.op x y) (M.op x y)) X0) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq12670 eq694
    | exact resolve eq694 eq12670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq12850 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (k (M.op x y) (M.op x y)) X0) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq12847 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12847
  have eq12855 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq733 eq12850
    | (have j1 := eq733 (M.op x y) x
       grind)
    | exact resolve eq12850 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733 eq12850
  have eq14550 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (k (M.op x y) (M.op x y))) X0) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq12855 eq16
    | exact resolve eq16 eq12855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12855
  have eq21975 : ∀ X0 : G, y = (M.op (M.op (M.op x y) y) X0) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2528 eq14550
    | exact resolve eq14550 eq2528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14550
  have eq22070 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq12670 eq21975
    | exact resolve eq21975 eq12670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21975
  have eq22154 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq22070 eq13
    | (have j0 := eq13 (M.op x y) (M.op x y)
       have j1 := eq22070 X0
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq22070 X0
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq22070 X0
       grind)
    | exact resolve eq13 eq22070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22070
  have eq22162 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq22154 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22154
  have eq22167 : ∀ X0 : G, y = (M.op (M.op x y) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2528 eq22162
    | (have j0 := eq22162 X0
       grind)
    | exact resolve eq22162 eq2528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2528 eq22162
  have eq22503 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22167 eq12670
    | exact resolve eq12670 eq22167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12670 eq22167
  have eq22576 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq22503
  have eq22618 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22576 eq27
    | exact resolve eq27 eq22576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22576
  have eq22624 : y = (M.op x y) := by
    first
    | (have r₁ := eq22618
       have r₂ := eq12686
       grind)
    | exact resolve eq22618 eq12686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22618
  have eq22626 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq22624
       grind)
    | exact superpose eq22624 eq24
    | exact resolve eq24 eq22624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq22624
  have eq22693 : (σ x) = (σ y) := by
    first
    | exact superpose eq12671 eq22626
    | exact resolve eq22626 eq12671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12671 eq22626
  have eq22734 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22693 eq2116
    | (have r₁ := eq2116
       have r₂ := eq22693
       grind)
    | exact resolve eq2116 eq22693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2116 eq22693
  have eq22798 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22734
  have eq22844 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq22798 eq27
    | exact resolve eq27 eq22798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq22798
  have eq22851 : False := by grind
  exact eq22851
