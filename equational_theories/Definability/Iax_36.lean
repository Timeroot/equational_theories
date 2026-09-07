import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pyx_Equation731 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq8 X0 (M.op X2 X2) X3
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
  have eq226 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 (M.op X2 X2) x
       have i₂ := eq21 X1 X0 X2 x
       grind)
    | (have i₁ := eq8 X0 (M.op X2 X2) X2
       have i₂ := eq21 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq575 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0))) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq226 X0 X2 X1
       have i₂ := eq12 X0 X2
       grind)
    | (have i₁ := eq226 X0 X0 X2
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq226
    | (have j1 := eq12 X0 X2
       grind)
    | exact resolve eq226 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq619 : ∀ X0 X2 : G, (k X0 X2) = (M.op X2 X0) ∨ X0 = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq575 X0 x X2
       have i₂ := eq226 X0 X0 x
       grind)
    | exact superpose eq226 eq575
    | (have j0 := eq575 X0 x X2
       grind)
    | exact resolve eq575 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq575
  have eq781 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq619 X1 (τ X0)
       grind)
    | exact superpose eq619 eq16
    | (have j1 := eq619 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq16 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq782 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq619 (σ X1) (σ X0)
       grind)
    | exact superpose eq619 eq13
    | (have j1 := eq619 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq13 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq9884 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq781 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq781
    | exact resolve eq781 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq9949 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9884 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq9884
    | (have j0 := eq9884 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq9884 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9884
  have eq67696 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq782 x y
       grind)
    | exact superpose eq782 eq14
    | (have j1 := eq782 x y
       grind)
    | exact resolve eq14 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq69233 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq67696
       have i₂ := eq9949 x y
       grind)
    | exact superpose eq9949 eq67696
    | (have j1 := eq9949 (σ x) (σ y)
       grind)
    | (have r₁ := eq67696
       have r₂ := eq9949 x y
       grind)
    | (have r₁ := eq67696
       have r₂ := eq9949 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq67696
       have r₂ := eq9949 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq67696 eq9949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9949 eq67696
  have eq69234 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq69233
  have eq69683 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq69234
       grind)
    | exact superpose eq69234 eq9
    | exact resolve eq9 eq69234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69234
  have eq69726 : x = y ∨ x = y := by
    first
    | (have i₁ := eq69683
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq69683
    | exact resolve eq69683 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69683
  have eq69727 : x = y := by grind
  clear eq69726
  have eq70392 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq69727
       grind)
    | exact superpose eq69727 eq14
    | exact resolve eq14 eq69727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69727
  have eq70393 : False := by grind
  exact eq70393

/-- `Equation765`: `x = y ◇ (z ◇ ((y ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pxx_pyx_Equation765 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law765 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law765.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X1 X2) X0))) = X0 := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 (M.op (M.op X1 X2) X0)) (M.op X0 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X1 (M.op X2 (M.op (M.op X1 X2) X0))
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op (M.op X1 X2) X3) X0)) = (M.op X1 (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X3 (M.op (M.op (M.op X1 X2) X3) X0)) X1 X2
       have i₂ := eq8 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (M.op X2 (M.op X1 X2)) X0) X1 X2
       have i₂ := eq8 X0 X2 (M.op X1 X2)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
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
  clear eq16
  have eq41 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
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
  have eq42 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X0 X2) := by
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
  have eq44 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq48 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq68 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X2) (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 (M.op X0 X2)
       have i₂ := eq23 X1 X0 X2
       grind)
    | exact superpose eq23 eq8
    | exact resolve eq8 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq133 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X1 X2 (M.op X0 X1)
       have i₂ := eq23 (M.op X1 X2) X0 X1
       grind)
    | exact superpose eq23 eq68
    | exact resolve eq68 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X2 (M.op (M.op (M.op X2 X1) X2) X0) X1
       have i₂ := eq8 X0 (M.op X2 X1) X2
       grind)
    | exact superpose eq8 eq68
    | exact resolve eq68 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X1 (M.op X1 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X2 (M.op X1 (M.op X1 X0)) (M.op X1 X0)
       have i₂ := eq68 X1 X0 (M.op X1 X0)
       grind)
    | exact superpose eq68 eq23
    | exact resolve eq23 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X1 X0 X1 X2
       have i₂ := eq23 (M.op X1 X2) (M.op X0 X1) X1
       grind)
    | exact superpose eq23 eq21
    | exact resolve eq21 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq206 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X0 X1) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq166 X1 (M.op X0 X1) X2
       have i₂ := eq23 (M.op (M.op X0 X1) X2) X0 X1
       grind)
    | exact superpose eq23 eq166
    | exact resolve eq166 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op X0 (M.op X1 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X3 (M.op (M.op X0 X1) X2) X2
       have i₂ := eq22 X2 X0 X1 X2
       grind)
    | exact superpose eq22 eq23
    | exact resolve eq23 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq275 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X3 X4)) X2) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op (M.op (M.op X0 X1) (M.op X3 X4)) X2) X3 X4
       have i₂ := eq22 X2 X0 X1 (M.op X3 X4)
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq438 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X1) X3) X2) X4) = (M.op (M.op (M.op X0 (M.op X1 X2)) X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq134 X4 (M.op (M.op (M.op X0 X1) X3) X2) X3
       have i₂ := eq22 X2 X0 X1 X3
       grind)
    | exact superpose eq22 eq134
    | exact resolve eq134 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq518 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X1) X3) X2) X4) = (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq438 X0 X1 X2 X3 X4
       have i₂ := eq265 X0 (M.op X1 X2) X3 X4
       grind)
    | exact superpose eq265 eq438
    | exact resolve eq438 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq529 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X3 X2)) X4) = (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq518 X0 X1 X2 X3 X4
       have i₂ := eq265 (M.op X0 X1) X3 X2 X4
       grind)
    | exact superpose eq265 eq518
    | exact resolve eq518 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq534 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X2 (M.op X0 (M.op X1 X4)))) = (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq529 X0 X1 X2 X3 X4
       have i₂ := eq275 X0 X1 X4 X3 X2
       grind)
    | exact superpose eq275 eq529
    | exact resolve eq529 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275 eq529
  have eq547 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  clear eq44
  have eq589 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) X3) = (M.op (M.op X2 X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq138 (M.op X1 (M.op (M.op X2 X1) X0)) X2 X3
       have i₂ := eq8 X0 X2 X1
       grind)
    | exact superpose eq8 eq138
    | exact resolve eq138 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq623 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X1 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq134 X2 (M.op X0 X1) X0
       have i₂ := eq138 X1 X0 X0
       grind)
    | exact superpose eq138 eq134
    | exact resolve eq134 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq646 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 (M.op X3 X0)) X1) (M.op X0 (M.op X1 X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq133 (M.op X3 (M.op X3 X0)) X1 X2
       have i₂ := eq138 X0 X3 (M.op X1 X2)
       grind)
    | exact superpose eq138 eq133
    | exact resolve eq133 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq655 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X3 X0) X1)) (M.op X0 (M.op X1 X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq646 X0 X1 X2 X3
       have i₂ := eq265 X3 (M.op X3 X0) X1 (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq265 eq646
    | exact resolve eq646 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq694 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) X3) = (M.op X0 (M.op X1 (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq589 X0 X1 X2 X3
       have i₂ := eq534 X1 X2 X1 X0 X3
       grind)
    | exact superpose eq534 eq589
    | exact resolve eq589 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq696 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X3 (M.op X3 (M.op X0 (M.op X1 X2)))))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq655 X0 X1 X2 X3
       have i₂ := eq534 X3 X3 X0 X1 (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq534 eq655
    | exact resolve eq655 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq702 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq696 X0 X1 X2 x
       have i₂ := eq694 X0 x X0 (M.op X1 X2)
       grind)
    | exact superpose eq694 eq696
    | exact resolve eq696 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq970 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op (M.op X2 (M.op (M.op X2 X1) X0)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq166 X1 (M.op X2 (M.op (M.op X2 X1) X0)) X3
       have i₂ := eq206 X2 X1 X0
       grind)
    | exact superpose eq206 eq166
    | exact resolve eq166 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq988 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X0 (M.op X1 (M.op X2 (M.op X2 X3)))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq970 X0 X1 X2 X3
       have i₂ := eq534 X2 X2 X1 X0 X3
       grind)
    | exact superpose eq534 eq970
    | exact resolve eq970 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534 eq970
  have eq1029 : ∀ X1 X2 X3 : G, (M.op (M.op X1 X1) (M.op X2 (M.op X2 X3))) = X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq988 x X1 X2 X3
       have i₂ := eq694 X1 x X1 (M.op X2 (M.op X2 X3))
       grind)
    | exact superpose eq694 eq988
    | exact resolve eq988 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694 eq988
  have eq1068 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq121 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1079 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq1068 (σ X0)
       grind)
    | exact superpose eq1068 eq13
    | exact resolve eq13 eq1068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1090 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1079 X0
       have i₂ := eq1068 X0
       grind)
    | exact superpose eq1068 eq1079
    | exact resolve eq1079 eq1068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068 eq1079
  have eq2225 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ (M.op X0 X0)) (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq702 (σ X0) X1 X2
       have i₂ := eq1090 X0
       grind)
    | exact superpose eq1090 eq702
    | exact resolve eq702 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2256 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X0) = (M.op (M.op X2 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq702 X2 (M.op X1 X1) (M.op (M.op X2 X2) X0)
       have i₂ := eq702 X1 (M.op X2 X2) X0
       grind)
    | exact superpose eq702 eq702
    | exact resolve eq702 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq3952 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op (M.op X1 X1) X0) ∨ (M.op X2 X3) = (k X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1029 X1 X2 (M.op X2 X0)
       have i₂ := eq41 X2 X0 X3
       grind)
    | exact superpose eq41 eq1029
    | (have j1 := eq41 X2 X1 X3
       grind)
    | exact resolve eq1029 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq3973 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq206 X1 X1 (M.op X2 (M.op X2 X0))
       have i₂ := eq1029 X1 X2 X0
       grind)
    | exact superpose eq1029 eq206
    | exact resolve eq206 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq4857 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X1)) ≠ (M.op (M.op X0 X0) (M.op X1 X1)) ∨ (M.op X2 (M.op X1 X1)) = (k (M.op X1 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq121 (M.op X1 X1) X2
       have i₂ := eq2256 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq121 (M.op X1 X1) X2
       have i₂ := eq2256 (M.op X1 X1) X0 X1
       grind)
    | exact superpose eq2256 eq121
    | (have j0 := eq121 (M.op X1 X1) X2
       grind)
    | (have r₁ := eq121 (M.op X1 X1) (M.op X2 X2)
       have r₂ := eq2256 (M.op X1 X1) X1 X2
       grind)
    | (have r₁ := eq121 (M.op X2 X2) (M.op X1 X1)
       have r₂ := eq2256 (M.op X2 X2) X1 X2
       grind)
    | exact resolve eq121 eq2256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq2256
  have eq4976 : ∀ X1 X2 : G, (M.op X2 (M.op X1 X1)) = (k (M.op X1 X1) X2) := by
    intro X1 X2
    first
    | (have j0 := eq4857 x X1 X2
       have j1 := eq3952 x X1 X2 (M.op X1 X1)
       grind)
    | (have r₁ := eq4857 X1 X1 X2
       have r₂ := eq3952 (M.op X1 X1) X1 X2 x
       grind)
    | (have r₁ := eq4857 x X1 (M.op X1 X1)
       have r₂ := eq3952 (M.op X1 X1) X1 (M.op x x) x
       grind)
    | exact resolve eq4857 eq3952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3952 eq4857
  have eq10403 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq547
       have i₂ := eq12 y x
       grind)
    | exact superpose eq12 eq547
    | (have j1 := eq12 x (σ x)
       grind)
    | exact resolve eq547 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq10407 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq10403
  have eq10410 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10407
       have i₂ := eq1090 x
       grind)
    | exact superpose eq1090 eq10407
    | exact resolve eq10407 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090 eq10407
  have eq10413 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq10410
       grind)
    | exact superpose eq10410 eq9
    | exact resolve eq9 eq10410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10410
  have eq10446 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10413
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq10413
    | exact resolve eq10413 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10413
  have eq10447 : x = (M.op x x) := by grind
  clear eq10446
  have eq10676 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq11 X0 x
       have i₂ := eq10447
       grind)
    | exact superpose eq10447 eq11
    | (have j0 := eq11 X0 x
       grind)
    | (have r₁ := eq11 X0 x
       have r₂ := eq10447
       grind)
    | exact resolve eq11 eq10447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10680 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1029 x X0 X1
       have i₂ := eq10447
       grind)
    | exact superpose eq10447 eq1029
    | exact resolve eq1029 eq10447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
  have eq10717 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op x (M.op x X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq265 x x X0 X1
       have i₂ := eq10447
       grind)
    | exact superpose eq10447 eq265
    | exact resolve eq265 eq10447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq10726 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq3973 x X0 x
       have i₂ := eq10447
       grind)
    | exact superpose eq10447 eq3973
    | exact resolve eq3973 eq10447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3973
  have eq10729 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq10676 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10676
  have eq10730 : ∀ X0 : G, x = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq10726 X0
       have i₂ := eq10447
       grind)
    | exact superpose eq10447 eq10726
    | exact resolve eq10726 eq10447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10726
  have eq10736 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10717 X0 X1
       have i₂ := eq138 X0 x X1
       grind)
    | exact superpose eq138 eq10717
    | exact resolve eq10717 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq10717
  have eq11232 : ∀ X0 X1 : G, (M.op X1 (k X0 x)) = (k (k X0 x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4976 X0 x
       have i₂ := eq10729 X0
       grind)
    | exact superpose eq10729 eq4976
    | exact resolve eq4976 eq10729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4976
  have eq11247 : ∀ X0 : G, (k X0 x) ≠ (k X0 x) ∨ (k X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq122 X0 X0
       have i₂ := eq10729 X0
       grind)
    | exact superpose eq10729 eq122
    | exact resolve eq122 eq10729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq11283 : ∀ X0 X1 : G, (M.op X1 (k (M.op X0 X1) x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 X1 X1
       have i₂ := eq10729 (M.op X0 X1)
       grind)
    | exact superpose eq10729 eq68
    | exact resolve eq68 eq10729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq11327 : ∀ X0 : G, (k X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq11247 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11247
  have eq11980 : ∀ X0 : G, x = (M.op (σ (M.op X0 X0)) x) := by
    intro X0
    first
    | (have i₁ := eq2225 X0 (σ (M.op X0 X0)) x
       have i₂ := eq10730 (σ (M.op X0 X0))
       grind)
    | exact superpose eq10730 eq2225
    | exact resolve eq2225 eq10730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2225 eq10730
  have eq12514 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (k (τ X0) x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 (τ X0)
       have i₂ := eq11327 (τ X0)
       grind)
    | (have i₁ := eq15 X0 x
       have i₂ := eq11327 (τ X0)
       grind)
    | exact superpose eq11327 eq15
    | exact resolve eq15 eq11327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12531 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq12514 X0
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq12514
    | exact resolve eq12514 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq12514
  have eq12546 : ∀ X0 : G, (k X0 X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq12531 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12531
    | exact resolve eq12531 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12531
  have eq14987 : x = (M.op (σ x) x) := by
    first
    | (have i₁ := eq11980 x
       have i₂ := eq10447
       grind)
    | exact superpose eq10447 eq11980
    | exact resolve eq11980 eq10447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10447 eq11980
  have eq15349 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq623 (σ x) x X0
       have i₂ := eq14987
       grind)
    | exact superpose eq14987 eq623
    | exact resolve eq623 eq14987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623 eq14987
  have eq15367 : ∀ X0 : G, (M.op x X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq15349 X0
       have i₂ := eq10736 (σ x) X0
       grind)
    | exact superpose eq10736 eq15349
    | exact resolve eq15349 eq10736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15349
  have eq15503 : ∀ X0 : G, (k X0 x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq11327 X0
       have i₂ := eq12546 X0
       grind)
    | (have i₁ := eq11327 (σ x)
       have i₂ := eq12546 (σ x)
       grind)
    | exact superpose eq12546 eq11327
    | exact resolve eq11327 eq12546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11327 eq12546
  have eq27670 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq15503 (σ X0)
       grind)
    | exact superpose eq15503 eq13
    | exact resolve eq13 eq15503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27672 : ∀ X0 X1 : G, (k (k (σ X0) x) (σ X1)) = (σ (k (k X0 (τ (σ x))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ x) X1
       have i₂ := eq15503 (σ X0)
       grind)
    | exact superpose eq15503 eq28
    | exact resolve eq28 eq15503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq15503
  have eq27683 : ∀ X0 X1 : G, (k (k (σ X0) x) (σ X1)) = (σ (k (k X0 x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27672 X0 X1
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq27672
    | exact resolve eq27672 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27672
  have eq27708 : ∀ X0 X1 : G, (k (k (σ X0) x) (σ X1)) = (σ (M.op X1 (k X0 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq27683 X0 X1
       have i₂ := eq11232 X0 X1
       grind)
    | exact superpose eq11232 eq27683
    | exact resolve eq27683 eq11232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27683
  have eq27725 : ∀ X0 X1 : G, (M.op (σ X1) (k (σ X0) x)) = (σ (M.op X1 (k X0 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq27708 X0 X1
       have i₂ := eq11232 (σ X0) (σ X1)
       grind)
    | exact superpose eq11232 eq27708
    | exact resolve eq27708 eq11232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11232 eq27708
  have eq27731 : ∀ X0 X1 : G, (σ (M.op X1 (k X0 x))) = (M.op (σ X1) (σ (k X0 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq27725 X0 X1
       have i₂ := eq27670 X0
       grind)
    | exact superpose eq27670 eq27725
    | exact resolve eq27725 eq27670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27725
  have eq41867 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq15367 (σ y)
       grind)
    | exact superpose eq15367 eq14
    | exact resolve eq14 eq15367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15367
  have eq51360 : ∀ X0 : G, (M.op x (M.op X0 (k X0 x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq10680 X0 X0
       have i₂ := eq10729 X0
       grind)
    | exact superpose eq10729 eq10680
    | exact resolve eq10680 eq10729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10680 eq10729
  have eq159540 : ∀ X0 : G, (σ X0) = (M.op x (M.op (σ X0) (σ (k X0 x)))) := by
    intro X0
    first
    | (have i₁ := eq51360 (σ X0)
       have i₂ := eq27670 X0
       grind)
    | exact superpose eq27670 eq51360
    | exact resolve eq51360 eq27670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27670 eq51360
  have eq159572 : ∀ X0 : G, (σ X0) = (M.op x (σ (M.op X0 (k X0 x)))) := by
    intro X0
    first
    | (have i₁ := eq159540 X0
       have i₂ := eq27731 X0 X0
       grind)
    | exact superpose eq27731 eq159540
    | exact resolve eq159540 eq27731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27731 eq159540
  have eq319752 : ∀ X0 : G, (σ (M.op x X0)) = (M.op x (σ (M.op X0 (k (M.op x X0) x)))) := by
    intro X0
    first
    | (have i₁ := eq159572 (M.op x X0)
       have i₂ := eq10736 X0 (k (M.op x X0) x)
       grind)
    | exact superpose eq10736 eq159572
    | exact resolve eq159572 eq10736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10736 eq159572
  have eq319848 : ∀ X0 : G, (σ (M.op x X0)) = (M.op x (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq319752 X0
       have i₂ := eq11283 x X0
       grind)
    | exact superpose eq11283 eq319752
    | exact resolve eq319752 eq11283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11283 eq319752
  have eq320127 : (M.op x (σ y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq41867
       have i₂ := eq319848 y
       grind)
    | exact superpose eq319848 eq41867
    | (have r₁ := eq41867
       have r₂ := eq319848 y
       grind)
    | exact resolve eq41867 eq319848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41867 eq319848
  have eq320156 : False := by grind
  exact eq320156

/-- `Equation8`: `x = x ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation8 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law8 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law8.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
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
  have eq25 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq26 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq30 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq25
    | exact resolve eq25 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq25 X1 (τ X0)
       grind)
    | exact superpose eq25 eq16
    | (have j1 := eq25 X1 (τ X0)
       grind)
    | exact resolve eq16 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq26 (σ X1) (σ X0)
       grind)
    | exact superpose eq26 eq13
    | (have j1 := eq26 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq27 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq27
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq27 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq27 x y
       grind)
    | exact superpose eq27 eq14
    | (have j1 := eq27 x y
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq9
    | (have j1 := eq27 X0 X1
       grind)
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq393 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq443 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq393 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq393
    | (have j0 := eq393 X0 X1
       grind)
    | exact resolve eq393 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq464 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq42
    | exact resolve eq42 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq504 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq464 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq464
    | (have j0 := eq464 X0 X1
       grind)
    | exact resolve eq464 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq548 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1
       have i₂ := eq443 X0 X1
       grind)
    | (have i₁ := eq8 X0
       have i₂ := eq443 (M.op X0 X0) X1
       grind)
    | exact superpose eq443 eq8
    | (have j1 := eq443 X0 X1
       grind)
    | exact resolve eq8 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq823 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8 (σ X0)
       have i₂ := eq38 X0 X0
       grind)
    | exact superpose eq38 eq8
    | (have j1 := eq38 X0 X0
       grind)
    | exact resolve eq8 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1160 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq119
       have i₂ := eq548 y x
       grind)
    | exact superpose eq548 eq119
    | (have j1 := eq548 y x
       grind)
    | (have r₁ := eq119
       have r₂ := eq548 y x
       grind)
    | exact resolve eq119 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq1161 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq119
       have i₂ := eq504 x y
       grind)
    | exact superpose eq504 eq119
    | (have j1 := eq504 x y
       grind)
    | (have r₁ := eq119
       have r₂ := eq504 x y
       grind)
    | exact resolve eq119 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq1162 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq119
       have i₂ := eq443 y x
       grind)
    | exact superpose eq443 eq119
    | (have j1 := eq443 (σ y) (σ x)
       grind)
    | (have r₁ := eq119
       have r₂ := eq443 y x
       grind)
    | exact resolve eq119 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq443
  have eq1163 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1162
  have eq1164 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by grind
  clear eq1161
  have eq1165 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1160
  have eq1179 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  have eq1180 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8 (σ x)
       have i₂ := eq1163
       grind)
    | exact superpose eq1163 eq8
    | exact resolve eq8 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq1183 : (σ y) = (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1179
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq1179
    | exact resolve eq1179 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179
  have eq1224 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq1241 : (k x y) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq1183
       grind)
    | exact superpose eq1183 eq9
    | exact resolve eq9 eq1183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183
  have eq1282 : y = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1241
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1241
    | exact resolve eq1241 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241
  have eq1333 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1282
       grind)
    | exact superpose eq1282 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq1282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282
  have eq1340 : y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq1333
  have eq1436 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq107 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq107
    | (have j0 := eq107 X1 (τ X0)
       grind)
    | exact resolve eq107 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq1532 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1436 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1436
    | (have j0 := eq1436 X0 X1
       grind)
    | exact resolve eq1436 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1436
  have eq1540 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1532 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1532
    | (have j0 := eq1532 X0 X1
       grind)
    | exact resolve eq1532 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1532
  have eq1858 : (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) := by grind
  clear eq1164
  have eq1862 : (σ y) = (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1858
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq1858
    | exact resolve eq1858 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1858
  have eq2004 : (k x y) = (τ (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq1862
       grind)
    | exact superpose eq1862 eq9
    | exact resolve eq9 eq1862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1862
  have eq2049 : y = (k x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq2004
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2004
    | exact resolve eq2004 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2004
  have eq2050 : y = (k x y) := by grind
  clear eq2049
  have eq2313 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26 y x
       have i₂ := eq2050
       grind)
    | exact superpose eq2050 eq26
    | (have j0 := eq26 y x
       grind)
    | exact resolve eq26 eq2050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2535 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq2313
  have eq3735 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq124 x x
       have i₂ := eq1165
       grind)
    | exact superpose eq1165 eq124
    | exact resolve eq124 eq1165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq1165
  have eq3750 : x = y ∨ (σ y) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3735
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3735
    | exact resolve eq3735 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3735
  have eq3751 : (σ y) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3750
       have r₂ := eq2535
       grind)
    | exact resolve eq3750 eq2535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3750
  have eq4135 : (k x x) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq3751
       grind)
    | exact superpose eq3751 eq9
    | exact resolve eq9 eq3751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3751
  have eq4194 : y = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4135
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq4135
    | exact resolve eq4135 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4135
  have eq4667 : y = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25 x x
       have i₂ := eq4194
       grind)
    | exact superpose eq4194 eq25
    | exact resolve eq25 eq4194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq4194
  have eq4674 : x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq4667
       have r₂ := eq2535
       grind)
    | exact resolve eq4667 eq2535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4667
  have eq5565 : x = y ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1340
       have i₂ := eq4674
       grind)
    | exact superpose eq4674 eq1340
    | exact resolve eq1340 eq4674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340 eq4674
  have eq5568 : y = (M.op x x) ∨ x = y := by grind
  clear eq5565
  have eq5987 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8 x
       have i₂ := eq5568
       grind)
    | exact superpose eq5568 eq8
    | exact resolve eq8 eq5568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5568
  have eq5989 : x = (M.op x y) := by
    first
    | (have r₁ := eq5987
       have r₂ := eq2535
       grind)
    | exact resolve eq5987 eq2535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2535 eq5987
  have eq7494 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1180
       grind)
    | exact superpose eq1180 eq14
    | exact resolve eq14 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180
  have eq7504 : (σ x) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq7494
       have i₂ := eq5989
       grind)
    | exact superpose eq5989 eq7494
    | exact resolve eq7494 eq5989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7494
  have eq7505 : y = (M.op x x) := by grind
  clear eq7504
  have eq7860 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1224 x y
       have i₂ := eq2050
       grind)
    | exact superpose eq2050 eq1224
    | (have j0 := eq1224 x y
       grind)
    | exact resolve eq1224 eq2050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224
  have eq8267 : y = (M.op x y) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq2050
       have i₂ := eq1540 x y
       grind)
    | exact superpose eq1540 eq2050
    | (have j1 := eq1540 x y
       grind)
    | exact resolve eq2050 eq1540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1540 eq2050
  have eq8364 : x = y ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq8267
       have i₂ := eq5989
       grind)
    | exact superpose eq5989 eq8267
    | exact resolve eq8267 eq5989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8267
  have eq8365 : y = (k x x) ∨ x = y := by grind
  clear eq8364
  have eq11234 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq823 x
       have i₂ := eq8365
       grind)
    | exact superpose eq8365 eq823
    | exact resolve eq823 eq8365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823 eq8365
  have eq11299 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq11234
       have r₂ := eq7860
       grind)
    | exact resolve eq11234 eq7860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11234
  have eq11343 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq11299
       grind)
    | exact superpose eq11299 eq14
    | exact resolve eq14 eq11299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11299
  have eq11369 : (σ x) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq11343
       have i₂ := eq5989
       grind)
    | exact superpose eq5989 eq11343
    | exact resolve eq11343 eq5989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5989 eq11343
  have eq11370 : x = y := by grind
  clear eq11369
  have eq11419 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq11370
       grind)
    | exact superpose eq11370 eq14
    | exact resolve eq14 eq11370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11440 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq7860
       have i₂ := eq11370
       grind)
    | exact superpose eq11370 eq7860
    | exact resolve eq7860 eq11370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7860
  have eq11443 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq11440
  have eq11451 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11419
       have i₂ := eq7505
       grind)
    | exact superpose eq7505 eq11419
    | exact resolve eq11419 eq7505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7505 eq11419
  have eq11453 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq11451
       have i₂ := eq11443
       grind)
    | exact superpose eq11443 eq11451
    | exact resolve eq11451 eq11443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11443 eq11451
  have eq11456 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq11453
       have i₂ := eq11370
       grind)
    | exact superpose eq11370 eq11453
    | exact resolve eq11453 eq11370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11370 eq11453
  have eq11457 : False := by grind
  exact eq11457

/-- `Equation820`: `x = x ◇ ((x ◇ x) ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation820 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law820 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law820.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X1 X1))) = X0 := by
    intro X0 X1
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
  have eq18 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq8 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq18 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq27 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq29 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
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
  clear eq17
  have eq52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq25
    | exact resolve eq25 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq25 X1 (τ X0)
       grind)
    | exact superpose eq25 eq16
    | (have j1 := eq25 X1 (τ X0)
       grind)
    | exact resolve eq16 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq58 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq25 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq22 (σ X1) (σ X0)
       grind)
    | exact superpose eq22 eq13
    | (have j1 := eq22 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (σ X0) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0
       have i₂ := eq12 (τ X0) X1
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
  have eq216 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq27 x y
       grind)
    | exact superpose eq27 eq14
    | (have j1 := eq27 x y
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq9
    | (have j1 := eq27 X0 X1
       grind)
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq27 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq470 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
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
  have eq509 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq10
    | (have j1 := eq35 X0 X1
       grind)
    | exact resolve eq10 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq529 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq470 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq470
    | (have j0 := eq470 X0 X1
       grind)
    | exact resolve eq470 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq552 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq57 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq57
    | exact resolve eq57 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq598 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq552 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq552
    | (have j0 := eq552 X0 X1
       grind)
    | exact resolve eq552 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq644 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1
       have i₂ := eq529 X0 X1
       grind)
    | (have i₁ := eq18 X0
       have i₂ := eq529 (M.op X0 X0) X1
       grind)
    | exact superpose eq529 eq18
    | (have j1 := eq529 X0 X1
       grind)
    | exact resolve eq18 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq838 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq18 (σ X0)
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq18
    | (have j1 := eq52 X0 X0
       grind)
    | exact resolve eq18 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1024 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq216
       have i₂ := eq644 y x
       grind)
    | exact superpose eq644 eq216
    | (have j1 := eq644 y x
       grind)
    | (have r₁ := eq216
       have r₂ := eq644 y x
       grind)
    | exact resolve eq216 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq1025 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq216
       have i₂ := eq598 x y
       grind)
    | exact superpose eq598 eq216
    | (have j1 := eq598 x y
       grind)
    | (have r₁ := eq216
       have r₂ := eq598 x y
       grind)
    | exact resolve eq216 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq1026 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq216
       have i₂ := eq529 y x
       grind)
    | exact superpose eq529 eq216
    | (have j1 := eq529 (σ y) (σ x)
       grind)
    | (have r₁ := eq216
       have r₂ := eq529 y x
       grind)
    | exact resolve eq216 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq1027 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1026
  have eq1028 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by grind
  clear eq1025
  have eq1029 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1024
  have eq1045 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  have eq1046 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18 (σ x)
       have i₂ := eq1027
       grind)
    | exact superpose eq1027 eq18
    | exact resolve eq18 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027
  have eq1052 : (σ y) = (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1045
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq1045
    | exact resolve eq1045 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq1197 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq529 y x
       have i₂ := eq1052
       grind)
    | exact superpose eq1052 eq529
    | (have j0 := eq529 y x
       grind)
    | exact resolve eq529 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq1198 : (k x y) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq1052
       grind)
    | exact superpose eq1052 eq9
    | exact resolve eq9 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052
  have eq1221 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq1197
  have eq1237 : y = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1198
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1198
    | exact resolve eq1198 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198
  have eq1343 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1237
       grind)
    | exact superpose eq1237 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq1237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237
  have eq1350 : y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq1343
  have eq1718 : (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) := by grind
  clear eq1028
  have eq1727 : (σ y) = (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1718
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq1718
    | exact resolve eq1718 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1718
  have eq1839 : (k x y) = (τ (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq1727
       grind)
    | exact superpose eq1727 eq9
    | exact resolve eq9 eq1727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1727
  have eq1878 : y = (k x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1839
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1839
    | exact resolve eq1839 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1839
  have eq1879 : y = (k x y) := by grind
  clear eq1878
  have eq1992 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22 y x
       have i₂ := eq1879
       grind)
    | exact superpose eq1879 eq22
    | (have j0 := eq22 y x
       grind)
    | exact resolve eq22 eq1879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1879
  have eq2054 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq1992
  have eq2546 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq226 x x
       have i₂ := eq1029
       grind)
    | exact superpose eq1029 eq226
    | exact resolve eq226 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq1029
  have eq2570 : x = y ∨ (σ y) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2546
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2546
    | exact resolve eq2546 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2546
  have eq2571 : (σ y) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2570
       have r₂ := eq2054
       grind)
    | exact resolve eq2570 eq2054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2570
  have eq2854 : (k x x) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq2571
       grind)
    | exact superpose eq2571 eq9
    | exact resolve eq9 eq2571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2571
  have eq2896 : y = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2854
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2854
    | exact resolve eq2854 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2854
  have eq3002 : y = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25 x x
       have i₂ := eq2896
       grind)
    | exact superpose eq2896 eq25
    | exact resolve eq25 eq2896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2896
  have eq3010 : x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq3002
       have r₂ := eq2054
       grind)
    | exact resolve eq3002 eq2054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3002
  have eq3349 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1221
       have i₂ := eq3010
       grind)
    | exact superpose eq3010 eq1221
    | exact resolve eq1221 eq3010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221
  have eq3350 : x = y ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1350
       have i₂ := eq3010
       grind)
    | exact superpose eq3010 eq1350
    | exact resolve eq1350 eq3010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1350 eq3010
  have eq3354 : y = (M.op x x) ∨ x = y := by grind
  clear eq3350
  have eq3355 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq3349
  have eq3612 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18 x
       have i₂ := eq3354
       grind)
    | exact superpose eq3354 eq18
    | exact resolve eq18 eq3354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3354
  have eq3625 : x = (M.op x y) := by
    first
    | (have r₁ := eq3612
       have r₂ := eq2054
       grind)
    | exact resolve eq3612 eq2054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2054 eq3612
  have eq6323 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1046
       grind)
    | exact superpose eq1046 eq14
    | exact resolve eq14 eq1046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046
  have eq6334 : (σ x) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6323
       have i₂ := eq3625
       grind)
    | exact superpose eq3625 eq6323
    | exact resolve eq6323 eq3625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6323
  have eq6335 : y = (M.op x x) := by grind
  clear eq6334
  have eq15194 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X1) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq168 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq168
    | (have j0 := eq168 X1 (σ X0)
       grind)
    | exact resolve eq168 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15225 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq244 (τ X0)
       have i₂ := eq168 (τ X0) X0
       grind)
    | exact superpose eq168 eq244
    | (have j0 := eq244 (τ X0)
       have j1 := eq168 (τ X0) X0
       grind)
    | exact resolve eq244 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq244
  have eq15270 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq15225 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15225
    | (have j0 := eq15225 X0
       grind)
    | exact resolve eq15225 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15225
  have eq15288 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15194 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq15194
    | (have j0 := eq15194 X0 X1
       grind)
    | exact resolve eq15194 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15194
  have eq15301 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (σ (τ X0)) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq15270 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15270
    | (have j0 := eq15270 X0
       grind)
    | exact resolve eq15270 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15270
  have eq15323 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq15301 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15301
    | (have j0 := eq15301 X0
       grind)
    | exact resolve eq15301 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15301
  have eq15339 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq15323 X0
       have j1 := eq58 X0 X0
       grind)
    | (have r₁ := eq15323 x
       have r₂ := eq58 x x
       grind)
    | exact resolve eq15323 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq15323
  have eq15360 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15339 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq15339
    | (have j0 := eq15339 (σ X0)
       grind)
    | exact resolve eq15339 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15339
  have eq15409 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15360 X0
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq15360
    | (have j0 := eq15360 X0
       grind)
    | exact resolve eq15360 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15360
  have eq15725 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq509 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq15726 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq15725 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15725
    | (have j0 := eq15725 X0
       grind)
    | exact resolve eq15725 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15725
  have eq15828 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq15726 (σ X0)
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq15726
    | (have j0 := eq15726 (σ X0)
       grind)
    | exact resolve eq15726 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15726
  have eq15846 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15828 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq15828
    | (have j0 := eq15828 X0
       grind)
    | exact resolve eq15828 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15828
  have eq16965 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq15409 x
       have i₂ := eq6335
       grind)
    | exact superpose eq6335 eq15409
    | (have j0 := eq15409 x
       grind)
    | exact resolve eq15409 eq6335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6335 eq15409
  have eq17692 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq15846 X0
       have i₂ := eq15288 X0 X0
       grind)
    | exact superpose eq15288 eq15846
    | (have j0 := eq15846 X0
       have j1 := eq15288 X0 X0
       grind)
    | (have r₁ := eq15846 X0
       have r₂ := eq15288 X0 X0
       grind)
    | exact resolve eq15846 eq15288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15288 eq15846
  have eq17708 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq17692 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17692
  have eq17956 : (σ x) = (σ y) ∨ y = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17708 x
       have i₂ := eq3355
       grind)
    | exact superpose eq3355 eq17708
    | exact resolve eq17708 eq3355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3355 eq17708
  have eq18102 : y = (k x x) ∨ (σ x) = (σ y) := by grind
  clear eq17956
  have eq18496 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq838 x
       have i₂ := eq18102
       grind)
    | exact superpose eq18102 eq838
    | exact resolve eq838 eq18102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838 eq18102
  have eq18563 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq18496
  have eq18902 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq18563
       grind)
    | exact superpose eq18563 eq14
    | exact resolve eq14 eq18563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18563
  have eq18937 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18902
       have i₂ := eq3625
       grind)
    | exact superpose eq3625 eq18902
    | exact resolve eq18902 eq3625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18902
  have eq18938 : (σ x) = (σ y) := by grind
  clear eq18937
  have eq19296 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq18938
       grind)
    | exact superpose eq18938 eq14
    | exact resolve eq14 eq18938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19300 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq16965
       have i₂ := eq18938
       grind)
    | exact superpose eq18938 eq16965
    | (have r₁ := eq16965
       have r₂ := eq18938
       grind)
    | exact resolve eq16965 eq18938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16965
  have eq19303 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq18938
       grind)
    | exact superpose eq18938 eq13
    | exact resolve eq13 eq18938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19381 : (σ x) = (σ (k x x)) := by grind
  clear eq19300
  have eq19396 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq19303 X0
       have i₂ := eq13 X0 x
       grind)
    | exact superpose eq13 eq19303
    | exact resolve eq19303 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19303
  have eq19399 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq19296
       have i₂ := eq3625
       grind)
    | exact superpose eq3625 eq19296
    | exact resolve eq19296 eq3625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19296
  have eq19524 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq139 x y
       grind)
    | exact superpose eq139 eq14
    | (have j1 := eq139 x y
       grind)
    | exact resolve eq14 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq19625 : (σ (M.op x y)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19524
       have i₂ := eq19396 x
       grind)
    | exact superpose eq19396 eq19524
    | exact resolve eq19524 eq19396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19396 eq19524
  have eq19636 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19625
       have i₂ := eq19381
       grind)
    | exact superpose eq19381 eq19625
    | exact resolve eq19625 eq19381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19381 eq19625
  have eq19637 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19636
       have i₂ := eq3625
       grind)
    | exact superpose eq3625 eq19636
    | exact resolve eq19636 eq3625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3625 eq19636
  have eq19638 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19637
  have eq19639 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq19638
       have i₂ := eq18938
       grind)
    | exact superpose eq18938 eq19638
    | exact resolve eq19638 eq18938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18938 eq19638
  have eq19640 : False := by grind
  exact eq19640

/-- `Equation820`: `x = x ◇ ((x ◇ x) ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pyx_pxy_Equation820 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law820 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law820.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X1 X1))) = X0 := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq22 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq8 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq40 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq63 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq35 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq156 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq63 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq189 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq156 (σ X0)
       grind)
    | exact superpose eq156 eq13
    | exact resolve eq13 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq189 X0
       have i₂ := eq156 X0
       grind)
    | exact superpose eq156 eq189
    | exact resolve eq189 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156 eq189
  have eq230 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq283 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq230
       have i₂ := eq196 x
       grind)
    | exact superpose eq196 eq230
    | exact resolve eq230 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq394 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0)
       have i₂ := eq196 X0
       grind)
    | exact superpose eq196 eq22
    | exact resolve eq22 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq1162 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq283
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq283
    | (have j1 := eq12 x y
       grind)
    | exact resolve eq283 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq1170 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq1162
  have eq1451 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq1170
       grind)
    | exact superpose eq1170 eq9
    | exact resolve eq9 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170
  have eq1490 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1451
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1451
    | exact resolve eq1451 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1451
  have eq1491 : y = (M.op x x) := by grind
  clear eq1490
  have eq1673 : x = (M.op x y) := by
    first
    | (have i₁ := eq22 x
       have i₂ := eq1491
       grind)
    | exact superpose eq1491 eq22
    | exact resolve eq22 eq1491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1683 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq394 x
       have i₂ := eq1491
       grind)
    | exact superpose eq1491 eq394
    | exact resolve eq394 eq1491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394 eq1491
  have eq2189 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1683
       grind)
    | exact superpose eq1683 eq14
    | exact resolve eq14 eq1683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1683
  have eq2193 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2189
       have i₂ := eq1673
       grind)
    | exact superpose eq1673 eq2189
    | exact resolve eq2189 eq1673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673 eq2189
  have eq2194 : False := by grind
  exact eq2194

/-- `Equation823`: `x = x ◇ ((x ◇ y) ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation823 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law823 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law823.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1))) = X0 := by
    intro X0 X1
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
  have eq18 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 (M.op (M.op X0 x) (M.op X0 x))
       have i₂ := eq8 X0 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq18 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq26 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq28 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq17
  have eq45 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq32
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq32 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq23
    | exact resolve eq23 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq22 (σ X1) (σ X0)
       grind)
    | exact superpose eq22 eq13
    | (have j1 := eq22 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq26 x y
       grind)
    | exact superpose eq26 eq14
    | (have j1 := eq26 x y
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq201 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (σ X0) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0
       have i₂ := eq12 (τ X0) X1
       grind)
    | (have i₁ := eq28 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq28
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq28 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq437 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
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
  have eq472 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq10
    | (have j1 := eq34 X0 X1
       grind)
    | exact resolve eq10 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq492 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq437 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq437
    | (have j0 := eq437 X0 X1
       grind)
    | exact resolve eq437 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq543 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1
       have i₂ := eq492 X0 X1
       grind)
    | (have i₁ := eq18 X0
       have i₂ := eq492 (M.op X0 X0) X1
       grind)
    | exact superpose eq492 eq18
    | (have j1 := eq492 X0 X1
       grind)
    | exact resolve eq18 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq544 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq827 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq18 (σ X0)
       have i₂ := eq51 X0 X0
       grind)
    | exact superpose eq51 eq18
    | (have j1 := eq51 X0 X0
       grind)
    | exact resolve eq18 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1029 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq162
       have i₂ := eq544 y x
       grind)
    | exact superpose eq544 eq162
    | (have j1 := eq544 y x
       grind)
    | (have r₁ := eq162
       have r₂ := eq544 y x
       grind)
    | exact resolve eq162 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq1030 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq162
       have i₂ := eq543 y x
       grind)
    | exact superpose eq543 eq162
    | (have j1 := eq543 y x
       grind)
    | (have r₁ := eq162
       have r₂ := eq543 y x
       grind)
    | exact resolve eq162 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq1031 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq162
       have i₂ := eq492 y x
       grind)
    | exact superpose eq492 eq162
    | (have j1 := eq492 (σ y) (σ x)
       grind)
    | (have r₁ := eq162
       have r₂ := eq492 y x
       grind)
    | exact resolve eq162 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq1032 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1031
  have eq1033 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1030
  have eq1034 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by grind
  clear eq1029
  have eq1049 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18 (σ x)
       have i₂ := eq1032
       grind)
    | exact superpose eq1032 eq18
    | exact resolve eq18 eq1032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1050 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  have eq1055 : (σ y) = (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1050
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq1050
    | exact resolve eq1050 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050
  have eq1203 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq492 y x
       have i₂ := eq1055
       grind)
    | exact superpose eq1055 eq492
    | (have j0 := eq492 y x
       grind)
    | exact resolve eq492 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492 eq1055
  have eq1228 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq1203
  have eq1833 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1033
  have eq1840 : (σ y) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1833
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq1833
    | exact resolve eq1833 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1833
  have eq1905 : (k x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq1840
       grind)
    | exact superpose eq1840 eq9
    | exact resolve eq9 eq1840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1840
  have eq1949 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1905
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1905
    | exact resolve eq1905 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1905
  have eq2018 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22 y x
       have i₂ := eq1949
       grind)
    | exact superpose eq1949 eq22
    | (have j0 := eq22 y x
       grind)
    | exact resolve eq22 eq1949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1949
  have eq2023 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2018
  have eq2154 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq2023
  have eq2999 : (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) := by grind
  clear eq1034
  have eq3010 : (σ y) = (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq2999
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq2999
    | exact resolve eq2999 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2999
  have eq3302 : (k x y) = (τ (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq3010
       grind)
    | exact superpose eq3010 eq9
    | exact resolve eq9 eq3010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3010
  have eq3357 : y = (k x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq3302
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3302
    | exact resolve eq3302 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3302
  have eq3358 : y = (k x y) := by grind
  clear eq3357
  have eq4449 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1049
       grind)
    | exact superpose eq1049 eq14
    | exact resolve eq14 eq1049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049
  have eq4948 : (σ x) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4449
       have i₂ := eq1228
       grind)
    | exact superpose eq1228 eq4449
    | exact resolve eq4449 eq1228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228
  have eq4949 : (σ x) ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq4948
  have eq10924 : (τ (σ y)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq45 (σ x) x
       have i₂ := eq1032
       grind)
    | exact superpose eq1032 eq45
    | exact resolve eq45 eq1032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq1032
  have eq11312 : (τ (σ y)) = (k (τ (σ x)) x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq10924
       have r₂ := eq4949
       grind)
    | exact resolve eq10924 eq4949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4949 eq10924
  have eq11362 : (k x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11312
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq11312
    | exact resolve eq11312 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11312
  have eq11369 : y = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11362
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq11362
    | exact resolve eq11362 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11362
  have eq11393 : y = (M.op x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq23 x x
       have i₂ := eq11369
       grind)
    | exact superpose eq11369 eq23
    | exact resolve eq23 eq11369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq11369
  have eq11403 : y = (M.op x x) ∨ x = y := by grind
  clear eq11393
  have eq11634 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18 x
       have i₂ := eq11403
       grind)
    | exact superpose eq11403 eq18
    | exact resolve eq18 eq11403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq11403
  have eq11646 : x = (M.op x y) := by
    first
    | (have r₁ := eq11634
       have r₂ := eq2154
       grind)
    | exact resolve eq11634 eq2154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2154 eq11634
  have eq11809 : (σ x) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4449
       have i₂ := eq11646
       grind)
    | exact superpose eq11646 eq4449
    | exact resolve eq4449 eq11646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4449
  have eq11814 : y = (M.op x x) := by grind
  clear eq11809
  have eq11994 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ X1) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq201 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq201
    | (have j0 := eq201 X1 (σ X0)
       grind)
    | exact resolve eq201 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq12082 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11994 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq11994
    | (have j0 := eq11994 X0 X1
       grind)
    | exact resolve eq11994 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11994
  have eq12432 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq472 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq12433 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq12432 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12432
    | (have j0 := eq12432 X0
       grind)
    | exact resolve eq12432 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12432
  have eq15045 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq137 x y
       grind)
    | exact superpose eq137 eq14
    | (have j1 := eq137 x y
       grind)
    | exact resolve eq14 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq15115 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15045
       have i₂ := eq3358
       grind)
    | exact superpose eq3358 eq15045
    | exact resolve eq15045 eq3358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3358 eq15045
  have eq15123 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15115
       have i₂ := eq11646
       grind)
    | exact superpose eq11646 eq15115
    | exact resolve eq15115 eq11646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15115
  have eq15679 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq12433 (σ X0)
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq12433
    | (have j0 := eq12433 (σ X0)
       grind)
    | exact resolve eq12433 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12433
  have eq15704 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15679 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq15679
    | (have j0 := eq15679 X0
       grind)
    | exact resolve eq15679 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15679
  have eq20798 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq15704 X0
       have i₂ := eq12082 X0 X0
       grind)
    | exact superpose eq12082 eq15704
    | (have j0 := eq15704 X0
       have j1 := eq12082 X0 X0
       grind)
    | (have r₁ := eq15704 X0
       have r₂ := eq12082 X0 X0
       grind)
    | exact resolve eq15704 eq12082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12082 eq15704
  have eq20817 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq20798 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20798
  have eq21464 : y = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq20817 x
       have i₂ := eq11814
       grind)
    | exact superpose eq11814 eq20817
    | exact resolve eq20817 eq11814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11814 eq20817
  have eq22234 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq827 x
       have i₂ := eq21464
       grind)
    | exact superpose eq21464 eq827
    | exact resolve eq827 eq21464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827 eq21464
  have eq22270 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq22234
  have eq22273 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq22270
       have r₂ := eq15123
       grind)
    | exact resolve eq22270 eq15123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15123 eq22270
  have eq22920 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq22273
       grind)
    | exact superpose eq22273 eq14
    | exact resolve eq14 eq22273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22273
  have eq22954 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq22920
       have i₂ := eq11646
       grind)
    | exact superpose eq11646 eq22920
    | exact resolve eq22920 eq11646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11646 eq22920
  have eq22955 : False := by grind
  exact eq22955

/-- `Equation827`: `x = x ◇ ((x ◇ y) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation827 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law827 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law827.models_iff G M).mp hM
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
  have eq52 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X1) = (k X0 X2) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X1 X1
       grind)
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X0 X1
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
  have eq689 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq690 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq689 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq699 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq690 (σ X0) (σ X1)
       grind)
    | exact superpose eq690 eq13
    | exact resolve eq13 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq716 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq699 X0 X1
       have i₂ := eq690 X0 X1
       grind)
    | exact superpose eq690 eq699
    | exact resolve eq699 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690 eq699
  have eq1297 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq716 x y
       grind)
    | exact superpose eq716 eq14
    | (have r₁ := eq14
       have r₂ := eq716 x y
       grind)
    | exact resolve eq14 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq1332 : False := by grind
  exact eq1332

/-- `Equation829`: `x = x ◇ ((x ◇ y) ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation829 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law829 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law829.models_iff G M).mp hM
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
  have eq56 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X1) = (k X0 X2) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X1 X1
       grind)
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X0 X1
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
  have eq977 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq978 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq977 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq987 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq978 (σ X0) (σ X1)
       grind)
    | exact superpose eq978 eq13
    | exact resolve eq13 eq978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1003 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq987 X0 X1
       have i₂ := eq978 X0 X1
       grind)
    | exact superpose eq978 eq987
    | exact resolve eq987 eq978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978 eq987
  have eq2382 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1003 x y
       grind)
    | exact superpose eq1003 eq14
    | (have r₁ := eq14
       have r₂ := eq1003 x y
       grind)
    | exact resolve eq14 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003
  have eq2421 : False := by grind
  exact eq2421
