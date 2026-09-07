import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation837`: `x = x ◇ ((y ◇ x) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation837 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law837 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law837.models_iff G M).mp hM
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
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
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
  have eq112 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
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
  have eq1352 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq112 x y
       grind)
    | exact superpose eq112 eq14
    | (have r₁ := eq14
       have r₂ := eq112 x y
       grind)
    | exact resolve eq14 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq1377 : False := by grind
  exact eq1377

/-- `Equation839`: `x = x ◇ ((y ◇ x) ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pyx_x_pyx_Equation839 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law839 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law839.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X1))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op (M.op (M.op X2 X0) (M.op X3 X2)) X1) X0)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 (M.op (M.op X2 X0) (M.op X3 X2)) X0
       have i₂ := eq8 X0 X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X0 X1) (M.op X1 (M.op (M.op X0 X1) X2))
       have i₂ := eq8 (M.op (M.op X0 X1) X2) X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 (M.op (M.op x x) X0) X1
       have i₂ := eq23 x x X0
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq48 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X1))) = X1 ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X1 X1
       have i₂ := eq12 (M.op X1 X1) X0
       grind)
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq12 (M.op x X1) (M.op X1 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 (M.op X1 X1) X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq53 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq56 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 (M.op X1 X0)
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq85 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X1)
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq11
    | (have j0 := eq11 X1 X0
       grind)
    | (have r₁ := eq11 X1 (M.op X1 X1)
       have r₂ := eq56 X1 X1
       grind)
    | exact resolve eq11 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq53
    | exact resolve eq53 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq53 X1 (τ X0)
       grind)
    | exact superpose eq53 eq16
    | (have j1 := eq53 X1 (τ X0)
       grind)
    | exact resolve eq16 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq94 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq102 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq12 X1 (σ X0)
       grind)
    | exact superpose eq12 eq20
    | (have j1 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq20 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq117 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X2 X3) (M.op X4 X2)) X0) X3) X5) X0) X1) X5)) = X1 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq22 X5 X1 (M.op (M.op (M.op (M.op X2 X3) (M.op X4 X2)) X0) X3) X0
       have i₂ := eq22 X3 X0 X2 X4
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (M.op X0 (M.op X1 X1)) X2) X1)) = X2 ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X1 X2 X1 X1
       have i₂ := eq12 (M.op X1 X1) X0
       grind)
    | (have i₁ := eq22 X0 X1 X2 x
       have i₂ := eq12 (M.op x X2) (M.op X2 X0)
       grind)
    | exact superpose eq12 eq22
    | (have j1 := eq12 (M.op X1 X1) X0
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq336 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq48 x x
       have i₂ := eq25 x x
       grind)
    | exact superpose eq25 eq48
    | exact resolve eq48 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq845 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op (σ (k X0 X1)) (M.op X2 (σ X1)))) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (σ X0) (σ X1) X2
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq8
    | (have j1 := eq50 X1 X0
       grind)
    | exact resolve eq8 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq855 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X1) (σ X0)
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq25
    | (have j1 := eq50 X1 X0
       grind)
    | exact resolve eq25 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq917 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq918 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1043 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X1 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq85 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq85
    | (have j0 := eq85 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq85 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq85 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq85 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1054 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq85 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq1057 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1043 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043
  have eq1103 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq71 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq1054 (σ X0)
       grind)
    | exact superpose eq1054 eq71
    | exact resolve eq71 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq1104 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq15 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq1054 (τ X0)
       grind)
    | exact superpose eq1054 eq15
    | exact resolve eq15 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq1054
  have eq1105 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1104 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1104
    | exact resolve eq1104 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq1106 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1103 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1103
    | exact resolve eq1103 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq1548 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq93 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq93
    | exact resolve eq93 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq1605 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1548 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1548
    | (have j0 := eq1548 X0 X1
       grind)
    | exact resolve eq1548 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548
  have eq1889 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) ∨ (k (M.op X1 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1057 X1 (M.op X0 X1)
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq1057
    | exact resolve eq1057 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq1948 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq89 y x
       grind)
    | exact superpose eq89 eq14
    | (have j1 := eq89 y x
       grind)
    | exact resolve eq14 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1962 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X1) (σ X0)
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq25
    | (have j1 := eq89 X0 X1
       grind)
    | exact resolve eq25 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4360 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq918 (τ X0) (τ X1)
       have i₂ := eq96 X0 X1
       grind)
    | exact superpose eq96 eq918
    | exact resolve eq918 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4386 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4360 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4360
    | (have j0 := eq4360 X0 X1
       grind)
    | exact resolve eq4360 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4360
  have eq4392 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4386 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq4386
    | (have j0 := eq4386 X0 X1
       grind)
    | exact resolve eq4386 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4386
  have eq4394 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4392 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4392
    | (have j0 := eq4392 X0 X1
       grind)
    | exact resolve eq4392 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4392
  have eq4395 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4394 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4394
    | (have j0 := eq4394 X0 X1
       grind)
    | exact resolve eq4394 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4394
  have eq4396 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4395 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq4395
    | (have j0 := eq4395 X0 X1
       grind)
    | exact resolve eq4395 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4395
  have eq4453 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq917 (τ X1) (τ X0)
       have i₂ := eq96 X1 X0
       grind)
    | exact superpose eq96 eq917
    | (have j0 := eq917 (τ X1) (τ X0)
       grind)
    | exact resolve eq917 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq4479 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4453 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4453
    | (have j0 := eq4453 X0 X1
       grind)
    | exact resolve eq4453 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4453
  have eq4484 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4479 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq4479
    | (have j0 := eq4479 X0 X1
       grind)
    | exact resolve eq4479 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4479
  have eq4485 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4484 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4484
    | (have j0 := eq4484 X0 X1
       grind)
    | exact resolve eq4484 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4484
  have eq4486 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4485 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4485
    | (have j0 := eq4485 X0 X1
       grind)
    | exact resolve eq4485 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4485
  have eq4741 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq4486 X0 (σ (M.op (τ X0) (τ X0)))
       have i₂ := eq1105 X0
       grind)
    | exact superpose eq1105 eq4486
    | (have j0 := eq4486 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | exact resolve eq4486 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4743 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq4486 X0 (τ (M.op (σ X0) (σ X0)))
       have i₂ := eq1106 X0
       grind)
    | exact superpose eq1106 eq4486
    | (have j0 := eq4486 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact resolve eq4486 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5520 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq1948
       have i₂ := eq1605 x y
       grind)
    | exact superpose eq1605 eq1948
    | (have j1 := eq1605 x y
       grind)
    | (have r₁ := eq1948
       have r₂ := eq1605 x y
       grind)
    | exact resolve eq1948 eq1605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1605 eq1948
  have eq5521 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by grind
  clear eq5520
  have eq5803 : (M.op x y) = (τ (σ y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq5521
       grind)
    | exact superpose eq5521 eq9
    | exact resolve eq9 eq5521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5521
  have eq5847 : y = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq5803
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq5803
    | exact resolve eq5803 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5803
  have eq5848 : y = (k y x) := by
    first
    | (have j1 := eq94 y x
       grind)
    | (have r₁ := eq5847
       have r₂ := eq94 y x
       grind)
    | exact resolve eq5847 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq5847
  have eq6154 : y ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq4486 y x
       have i₂ := eq5848
       grind)
    | exact superpose eq5848 eq4486
    | (have j0 := eq4486 y x
       grind)
    | exact resolve eq4486 eq5848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4486
  have eq7243 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X1) X0)) = X1 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq126 X1 X1 x
       have i₂ := eq25 X1 X1
       grind)
    | exact superpose eq25 eq126
    | exact resolve eq126 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq9684 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7243 X0 (M.op X1 X0)
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq7243
    | (have j0 := eq7243 X0 X1
       grind)
    | exact resolve eq7243 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7243
  have eq10818 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (M.op (σ (τ (k X0 X1))) (M.op X2 (σ (τ X1))))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq845 (τ X0) (τ X1) X2
       have i₂ := eq96 X1 X0
       grind)
    | exact superpose eq96 eq845
    | (have j0 := eq845 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq845 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq10978 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (M.op (σ (τ (k X0 X1))) (M.op X2 X1))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10818 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq10818
    | (have j0 := eq10818 X0 X1 X2
       grind)
    | exact resolve eq10818 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10818
  have eq10989 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (M.op (k X0 X1) (M.op X2 X1))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10978 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq10978
    | (have j0 := eq10978 X0 X1 X2
       grind)
    | exact resolve eq10978 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10978
  have eq10992 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (k X0 X1) (M.op X2 X1))) = X0 ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10989 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10989
    | (have j0 := eq10989 X0 X1 X2
       grind)
    | exact resolve eq10989 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10989
  have eq10993 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 (M.op (k X0 X1) (M.op X2 X1))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10992 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10992
    | (have j0 := eq10992 X0 X1 X2
       grind)
    | exact resolve eq10992 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10992
  have eq10994 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (k X0 X1) (M.op X2 X1))) = X0 ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10993 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq10993
    | (have j0 := eq10993 X0 X1 X2
       grind)
    | exact resolve eq10993 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10993
  have eq11957 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1889 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1889
  have eq18258 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1962 (τ X1) (τ X0)
       have i₂ := eq96 X0 X1
       grind)
    | exact superpose eq96 eq1962
    | exact resolve eq1962 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18440 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18258 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq18258
    | (have j0 := eq18258 X0 X1
       grind)
    | exact resolve eq18258 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18258
  have eq18455 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18440 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18440
    | (have j0 := eq18440 X0 X1
       grind)
    | exact resolve eq18440 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18440
  have eq18461 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (M.op X0 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18455 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq18455
    | (have j0 := eq18455 X0 X1
       grind)
    | exact resolve eq18455 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18455
  have eq18462 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18461 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18461
    | (have j0 := eq18461 X0 X1
       grind)
    | exact resolve eq18461 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18461
  have eq18903 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ (k X0 X1))) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18462 (τ X1) (τ X0)
       have i₂ := eq96 X0 X1
       grind)
    | exact superpose eq96 eq18462
    | exact resolve eq18462 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18462
  have eq33838 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq102 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq102
    | exact resolve eq102 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq34455 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq33838 X0 X1
       have i₂ := eq96 X0 X1
       grind)
    | exact superpose eq96 eq33838
    | (have j0 := eq33838 X0 X1
       grind)
    | exact resolve eq33838 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq33838
  have eq35311 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq336 X1
       have i₂ := eq34455 X1 X1
       grind)
    | (have i₁ := eq336 X1
       have i₂ := eq34455 X0 X1
       grind)
    | exact superpose eq34455 eq336
    | (have j1 := eq34455 X0 X1
       grind)
    | exact resolve eq336 eq34455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336 eq34455
  have eq35686 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = X1 ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq35311 X0 X1
       have j1 := eq11957 X0 X1
       grind)
    | (have r₁ := eq35311 X0 X1
       have r₂ := eq11957 X0 X1
       grind)
    | exact resolve eq35311 eq11957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11957 eq35311
  have eq54594 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k (M.op X0 X0) X1) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4396 (M.op X0 X0) X1
       have i₂ := eq9684 X0 X0
       grind)
    | exact superpose eq9684 eq4396
    | (have j0 := eq4396 (M.op X0 X0) X1
       have j1 := eq9684 X0 X1
       grind)
    | exact resolve eq4396 eq9684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4396 eq9684
  have eq54810 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq54594 X0 X1
       have j1 := eq53 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq54594 X0 X1
       have r₂ := eq53 (M.op X0 X0) X1
       grind)
    | exact resolve eq54594 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq54594
  have eq55908 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10994 X0 X1 (M.op (M.op (M.op (M.op (M.op (M.op (M.op x x) (M.op x x)) x) x) X1) x) (k X0 X1))
       have i₂ := eq117 x (k X0 X1) x x x X1
       grind)
    | exact superpose eq117 eq10994
    | (have j0 := eq10994 X0 X1 x
       grind)
    | exact resolve eq10994 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq10994
  have eq57058 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (M.op (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq55908 X0 (σ (M.op (τ X0) (τ X0)))
       have i₂ := eq1105 X0
       grind)
    | exact superpose eq1105 eq55908
    | (have j0 := eq55908 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | exact resolve eq55908 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105
  have eq57061 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (M.op (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq55908 X0 (τ (M.op (σ X0) (σ X0)))
       have i₂ := eq1106 X0
       grind)
    | exact superpose eq1106 eq55908
    | (have j0 := eq55908 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact resolve eq55908 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57092 : y = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq55908 y x
       have i₂ := eq5848
       grind)
    | exact superpose eq5848 eq55908
    | (have j0 := eq55908 y x
       grind)
    | exact resolve eq55908 eq5848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55908
  have eq57385 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq57092
       have r₂ := eq6154
       grind)
    | exact resolve eq57092 eq6154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6154 eq57092
  have eq57390 : ∀ X0 : G, (M.op X0 X0) = (M.op (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have j0 := eq57061 X0
       have j1 := eq4743 X0
       grind)
    | (have r₁ := eq57061 X0
       have r₂ := eq4743 X0
       grind)
    | exact resolve eq57061 eq4743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4743 eq57061
  have eq57393 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have j0 := eq57058 X0
       have j1 := eq4741 X0
       grind)
    | (have r₁ := eq57058 X0
       have r₂ := eq4741 X0
       grind)
    | exact resolve eq57058 eq4741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4741 eq57058
  have eq61588 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq57390 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq57390
    | exact resolve eq57390 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61820 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (τ (M.op X0 X0)) = (τ (k X0 (τ (M.op (σ X0) (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq35686 (τ (M.op (σ X0) (σ X0))) X0
       have i₂ := eq57390 X0
       grind)
    | exact superpose eq57390 eq35686
    | (have j0 := eq35686 X0 X0
       grind)
    | exact resolve eq35686 eq57390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35686 eq57390
  have eq61871 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq61820 X0
       have i₂ := eq1106 X0
       grind)
    | exact superpose eq1106 eq61820
    | (have j0 := eq61820 X0
       grind)
    | exact resolve eq61820 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106 eq61820
  have eq62626 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq57393 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq57393
    | exact resolve eq57393 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57393
  have eq64920 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq62626 y
       have i₂ := eq57385
       grind)
    | exact superpose eq57385 eq62626
    | exact resolve eq62626 eq57385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62626
  have eq66320 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op (σ y) (σ y)) (M.op X0 (σ (M.op x y))))) := by
    intro X0
    first
    | (have i₁ := eq8 (σ y) (σ (M.op x y)) X0
       have i₂ := eq64920
       grind)
    | exact superpose eq64920 eq8
    | exact resolve eq8 eq64920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68591 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq18903 (M.op X0 X0) X0
       have i₂ := eq61871 X0
       grind)
    | exact superpose eq61871 eq18903
    | (have j1 := eq61871 X0
       grind)
    | exact resolve eq18903 eq61871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18903 eq61871
  have eq68607 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq68591 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68591
  have eq68616 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68607 X0
       have i₂ := eq61588 X0
       grind)
    | exact superpose eq61588 eq68607
    | (have j0 := eq68607 X0
       grind)
    | exact resolve eq68607 eq61588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61588 eq68607
  have eq91480 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq68616 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq68616
    | exact resolve eq68616 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68616
  have eq102492 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq855 y x
       have i₂ := eq5848
       grind)
    | exact superpose eq5848 eq855
    | (have j0 := eq855 y x
       grind)
    | exact resolve eq855 eq5848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq104633 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq54810 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54810
  have eq104634 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq104633 X0
       grind)
    | (have r₁ := eq104633 X0
       have r₂ := eq25 X0 X0
       grind)
    | exact resolve eq104633 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104633
  have eq104753 : y = (k (M.op x y) y) := by
    first
    | (have i₁ := eq104634 y
       have i₂ := eq57385
       grind)
    | exact superpose eq57385 eq104634
    | exact resolve eq104634 eq57385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104634
  have eq104917 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1962 (M.op x y) y
       have i₂ := eq104753
       grind)
    | exact superpose eq104753 eq1962
    | exact resolve eq1962 eq104753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1962 eq104753
  have eq104956 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq104917
       have i₂ := eq64920
       grind)
    | exact superpose eq64920 eq104917
    | exact resolve eq104917 eq64920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104917
  have eq120780 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ X0))
       have i₂ := eq91480 X0
       grind)
    | exact superpose eq91480 eq10
    | (have j1 := eq91480 X0
       grind)
    | exact resolve eq10 eq91480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91480
  have eq122723 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ X0))
       have i₂ := eq120780 X0
       grind)
    | exact superpose eq120780 eq10
    | (have j1 := eq120780 X0
       grind)
    | exact resolve eq10 eq120780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120780
  have eq123091 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ (M.op y y)) (M.op X0 (σ (M.op x y))))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq66320 X0
       have i₂ := eq122723 y
       grind)
    | exact superpose eq122723 eq66320
    | (have j1 := eq122723 y
       grind)
    | exact resolve eq66320 eq122723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66320 eq122723
  have eq123164 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y))))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq123091 X0
       have i₂ := eq57385
       grind)
    | exact superpose eq57385 eq123091
    | exact resolve eq123091 eq57385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57385 eq123091
  have eq123192 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq123164 x
       have i₂ := eq25 x (σ (M.op x y))
       grind)
    | exact superpose eq25 eq123164
    | exact resolve eq123164 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123164
  have eq124964 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq25 (σ y) (σ (M.op x y))
       have i₂ := eq123192
       grind)
    | exact superpose eq123192 eq25
    | exact resolve eq25 eq123192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq123192
  have eq124987 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq124964
       have i₂ := eq64920
       grind)
    | exact superpose eq64920 eq124964
    | exact resolve eq124964 eq64920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64920 eq124964
  have eq129228 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq102492
       have i₂ := eq104956
       grind)
    | exact superpose eq104956 eq102492
    | exact resolve eq102492 eq104956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104956
  have eq129239 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq124987
       have i₂ := eq102492
       grind)
    | exact superpose eq102492 eq124987
    | exact resolve eq124987 eq102492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124987
  have eq129298 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq102492
  have eq129302 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq129228
  have eq129324 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq129239
       have r₂ := eq129298
       grind)
    | exact resolve eq129239 eq129298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129239 eq129298
  have eq129333 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq129302
       have r₂ := eq14
       grind)
    | exact resolve eq129302 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129302
  have eq129347 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq129324
       have r₂ := eq14
       grind)
    | exact resolve eq129324 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129324
  have eq129392 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 (M.op x y) X0
       have i₂ := eq129333
       grind)
    | exact superpose eq129333 eq13
    | exact resolve eq13 eq129333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129408 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (σ (k (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq89 (M.op x y) x
       have i₂ := eq129333
       grind)
    | exact superpose eq129333 eq89
    | exact resolve eq89 eq129333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq129426 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ (σ (k (M.op x y) X0)) ∨ (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq918 X0 (M.op x y)
       have i₂ := eq129333
       grind)
    | exact superpose eq129333 eq918
    | exact resolve eq918 eq129333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918
  have eq129553 : ∀ X0 : G, (σ y) ≠ (σ (k (M.op x y) X0)) ∨ (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq129426 X0
       have i₂ := eq129347
       grind)
    | exact superpose eq129347 eq129426
    | (have j0 := eq129426 X0
       grind)
    | exact resolve eq129426 eq129347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129347 eq129426
  have eq129576 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (σ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq129392 X0
       have i₂ := eq13 y X0
       grind)
    | exact superpose eq13 eq129392
    | exact resolve eq129392 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129392
  have eq129596 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq129553 X0
       have j1 := eq129408 X0
       grind)
    | (have r₁ := eq129553 X0
       have r₂ := eq129408 X0
       grind)
    | exact resolve eq129553 eq129408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129408 eq129553
  have eq129607 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq129596 X0
       have i₂ := eq129576 X0
       grind)
    | exact superpose eq129576 eq129596
    | exact resolve eq129596 eq129576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129576 eq129596
  have eq134050 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq129607 x
       grind)
    | exact superpose eq129607 eq14
    | exact resolve eq14 eq129607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129607
  have eq134551 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq134050
       have i₂ := eq5848
       grind)
    | exact superpose eq5848 eq134050
    | exact resolve eq134050 eq5848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5848 eq134050
  have eq134760 : False := by grind
  exact eq134760

/-- `Equation840`: `x = x ◇ ((y ◇ x) ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pyx_x_pyx_Equation840 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law840 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law840.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq22 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq8 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 (M.op X1 X0)
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq43 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X1))) = X1 ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X1 X1
       have i₂ := eq12 (M.op X1 X1) X0
       grind)
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq12 (M.op x x) (M.op X1 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 (M.op X1 X1) X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq47 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X1)
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq11
    | (have j0 := eq11 X1 X0
       grind)
    | (have r₁ := eq11 X1 (M.op X1 X1)
       have r₂ := eq24 X1 X1
       grind)
    | exact resolve eq11 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq64 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq68 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq47
    | exact resolve eq47 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq47 X1 (τ X0)
       grind)
    | exact superpose eq47 eq16
    | (have j1 := eq47 X1 (τ X0)
       grind)
    | exact resolve eq16 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X2 X2))) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X1 (M.op X0 X0)) X0 X2
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq8
    | (have j1 := eq43 X1 X0
       grind)
    | exact resolve eq8 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq437 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) (σ X0)
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq22
    | (have j1 := eq44 X1 X0
       grind)
    | exact resolve eq22 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq484 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq485 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq516 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq54 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq606 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq64 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq516 (σ X0)
       grind)
    | exact superpose eq516 eq64
    | exact resolve eq64 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq607 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq15 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq516 (τ X0)
       grind)
    | exact superpose eq516 eq15
    | exact resolve eq15 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq608 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq607 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq607
    | exact resolve eq607 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq609 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq606 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq606
    | exact resolve eq606 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq666 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq15 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq608 (τ X0)
       grind)
    | exact superpose eq608 eq15
    | exact resolve eq15 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq667 : ∀ X0 : G, (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq666 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq666
    | exact resolve eq666 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq736 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op (σ (σ X0)) (σ (σ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq64 X0 (τ (M.op (σ (σ X0)) (σ (σ X0))))
       have i₂ := eq609 (σ X0)
       grind)
    | exact superpose eq609 eq64
    | exact resolve eq64 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq741 : ∀ X0 : G, (k X0 (τ (τ (M.op (σ (σ X0)) (σ (σ X0)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq736 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq736
    | exact resolve eq736 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq924 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq84 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq84
    | exact resolve eq84 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq969 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq924 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq924
    | (have j0 := eq924 X0 X1
       grind)
    | exact resolve eq924 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq1245 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq79 y x
       grind)
    | exact superpose eq79 eq14
    | (have j1 := eq79 y x
       grind)
    | exact resolve eq14 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1253 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) (σ X0)
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq22
    | (have j1 := eq79 X0 X1
       grind)
    | exact resolve eq22 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2699 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq485 (τ X0) (τ X1)
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq485
    | exact resolve eq485 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2725 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2699 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2699
    | (have j0 := eq2699 X0 X1
       grind)
    | exact resolve eq2699 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2699
  have eq2731 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2725 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq2725
    | (have j0 := eq2725 X0 X1
       grind)
    | exact resolve eq2725 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725
  have eq2733 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2731 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2731
    | (have j0 := eq2731 X0 X1
       grind)
    | exact resolve eq2731 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2731
  have eq2734 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2733 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2733
    | (have j0 := eq2733 X0 X1
       grind)
    | exact resolve eq2733 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2733
  have eq2735 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2734 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq2734
    | (have j0 := eq2734 X0 X1
       grind)
    | exact resolve eq2734 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2734
  have eq2793 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq437 X0 (M.op X0 X0)
       have i₂ := eq516 X0
       grind)
    | exact superpose eq516 eq437
    | (have j0 := eq437 X0 (M.op X0 X0)
       grind)
    | exact resolve eq437 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2806 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq437 (τ X0) (τ X1)
       have i₂ := eq68 X1 X0
       grind)
    | exact superpose eq68 eq437
    | (have j0 := eq437 (τ X0) (τ X1)
       grind)
    | exact resolve eq437 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2859 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2806 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq2806
    | (have j0 := eq2806 X0 X1
       grind)
    | exact resolve eq2806 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2806
  have eq2866 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2859 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2859
    | (have j0 := eq2859 X0 X1
       grind)
    | exact resolve eq2859 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2859
  have eq2868 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2866 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2866
    | (have j0 := eq2866 X0 X1
       grind)
    | exact resolve eq2866 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2866
  have eq2869 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2868 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2868
    | (have j0 := eq2868 X0 X1
       grind)
    | exact resolve eq2868 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2868
  have eq2908 : ∀ X0 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq484 (M.op X0 X0) X0
       have i₂ := eq516 X0
       grind)
    | exact superpose eq516 eq484
    | (have j0 := eq484 (M.op X0 X0) X0
       grind)
    | exact resolve eq484 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq2918 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq484 (τ X1) (τ X0)
       have i₂ := eq68 X1 X0
       grind)
    | exact superpose eq68 eq484
    | (have j0 := eq484 (τ X1) (τ X0)
       grind)
    | exact resolve eq484 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq2944 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2918 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2918
    | (have j0 := eq2918 X0 X1
       grind)
    | exact resolve eq2918 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2918
  have eq2950 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2908 X0
       have j1 := eq2793 X0
       grind)
    | (have r₁ := eq2908 X0
       have r₂ := eq2793 X0
       grind)
    | exact resolve eq2908 eq2793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2793 eq2908
  have eq2953 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2944 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq2944
    | (have j0 := eq2944 X0 X1
       grind)
    | exact resolve eq2944 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2944
  have eq2955 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2953 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2953
    | (have j0 := eq2953 X0 X1
       grind)
    | exact resolve eq2953 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2953
  have eq2956 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2955 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2955
    | (have j0 := eq2955 X0 X1
       grind)
    | exact resolve eq2955 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2955
  have eq3340 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (M.op (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq2869 X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))
       have i₂ := eq667 X0
       grind)
    | exact superpose eq667 eq2869
    | (have j0 := eq2869 X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))
       grind)
    | exact resolve eq2869 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3341 : ∀ X0 : G, (M.op X0 X0) = (M.op (τ (M.op (σ X0) (σ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2869 X0 (τ (M.op (σ X0) (σ X0)))
       have i₂ := eq609 X0
       grind)
    | exact superpose eq609 eq2869
    | (have j0 := eq2869 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact resolve eq2869 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3342 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (M.op (τ (τ (M.op (σ (σ X0)) (σ (σ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq2869 X0 (τ (τ (M.op (σ (σ X0)) (σ (σ X0)))))
       have i₂ := eq741 X0
       grind)
    | exact superpose eq741 eq2869
    | (have j0 := eq2869 X0 (τ (τ (M.op (σ (σ X0)) (σ (σ X0)))))
       grind)
    | exact resolve eq2869 eq741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3526 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq2956 X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))
       have i₂ := eq667 X0
       grind)
    | exact superpose eq667 eq2956
    | (have j0 := eq2956 X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))
       grind)
    | exact resolve eq2956 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq3527 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq2956 X0 (τ (M.op (σ X0) (σ X0)))
       have i₂ := eq609 X0
       grind)
    | exact superpose eq609 eq2956
    | (have j0 := eq2956 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact resolve eq2956 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3528 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op (τ (τ (M.op (σ (σ X0)) (σ (σ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq2956 X0 (τ (τ (M.op (σ (σ X0)) (σ (σ X0)))))
       have i₂ := eq741 X0
       grind)
    | exact superpose eq741 eq2956
    | (have j0 := eq2956 X0 (τ (τ (M.op (σ (σ X0)) (σ (σ X0)))))
       grind)
    | exact resolve eq2956 eq741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq3537 : ∀ X0 : G, (M.op X0 X0) = (M.op (τ (τ (M.op (σ (σ X0)) (σ (σ X0))))) X0) := by
    intro X0
    first
    | (have j0 := eq3528 X0
       have j1 := eq3342 X0
       grind)
    | (have r₁ := eq3528 X0
       have r₂ := eq3342 X0
       grind)
    | exact resolve eq3528 eq3342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3342 eq3528
  have eq3538 : ∀ X0 : G, (M.op X0 X0) = (M.op (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have j0 := eq3527 X0
       have j1 := eq3341 X0
       grind)
    | (have r₁ := eq3527 X0
       have r₂ := eq3341 X0
       grind)
    | exact resolve eq3527 eq3341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3341 eq3527
  have eq3539 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) := by
    intro X0
    first
    | (have j0 := eq3526 X0
       have j1 := eq3340 X0
       grind)
    | (have r₁ := eq3526 X0
       have r₂ := eq3340 X0
       grind)
    | exact resolve eq3526 eq3340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3340 eq3526
  have eq3698 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq3538 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3538
    | exact resolve eq3538 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3538
  have eq5328 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq1245
       have i₂ := eq969 x y
       grind)
    | exact superpose eq969 eq1245
    | (have j1 := eq969 x y
       grind)
    | (have r₁ := eq1245
       have r₂ := eq969 x y
       grind)
    | exact resolve eq1245 eq969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969 eq1245
  have eq5329 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by grind
  clear eq5328
  have eq5495 : (M.op x y) = (τ (σ y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq5329
       grind)
    | exact superpose eq5329 eq9
    | exact resolve eq9 eq5329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5329
  have eq5547 : y = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq5495
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq5495
    | exact resolve eq5495 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5495
  have eq5548 : y = (k y x) := by
    first
    | (have j1 := eq85 y x
       grind)
    | (have r₁ := eq5547
       have r₂ := eq85 y x
       grind)
    | exact resolve eq5547 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq5547
  have eq5651 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq437 y x
       have i₂ := eq5548
       grind)
    | exact superpose eq5548 eq437
    | (have j0 := eq437 y x
       grind)
    | exact resolve eq437 eq5548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq5653 : y = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq2869 y x
       have i₂ := eq5548
       grind)
    | exact superpose eq5548 eq2869
    | (have j0 := eq2869 y x
       grind)
    | exact resolve eq2869 eq5548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2869
  have eq5654 : y ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq2956 y x
       have i₂ := eq5548
       grind)
    | exact superpose eq5548 eq2956
    | (have j0 := eq2956 y x
       grind)
    | exact resolve eq2956 eq5548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2956
  have eq5655 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq5653
       have r₂ := eq5654
       grind)
    | exact resolve eq5653 eq5654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5653 eq5654
  have eq5749 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq2950 y
       have i₂ := eq5655
       grind)
    | exact superpose eq5655 eq2950
    | exact resolve eq2950 eq5655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2950
  have eq6502 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (k (M.op X0 (M.op X0 X0)) X1) ∨ (M.op X1 (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op X0 X0)) X1) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2735 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq169 X0 X0 X0
       grind)
    | exact superpose eq169 eq2735
    | (have j0 := eq2735 (M.op X0 (M.op X0 X0)) X1
       have j1 := eq169 X0 X0 x
       grind)
    | (have r₁ := eq2735 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq169 X0 (M.op X0 X0) x
       grind)
    | exact resolve eq2735 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169 eq2735
  have eq6557 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op X0 X0)) X1) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0 X1
    first
    | (have j0 := eq6502 X0 X1
       have j1 := eq47 (M.op X0 (M.op X0 X0)) X1
       grind)
    | (have r₁ := eq6502 X0 X1
       have r₂ := eq47 (M.op X0 (M.op X0 X0)) X1
       grind)
    | exact resolve eq6502 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq6502
  have eq6570 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6557 X0 X1
       have i₂ := eq22 X0 X0
       grind)
    | exact superpose eq22 eq6557
    | (have j0 := eq6557 X0 X1
       grind)
    | exact resolve eq6557 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6557
  have eq6576 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6570 X0 X1
       have i₂ := eq22 X0 X0
       grind)
    | exact superpose eq22 eq6570
    | (have j0 := eq6570 X0 X1
       grind)
    | exact resolve eq6570 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6570
  have eq10892 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (k (M.op X1 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq6576 X1 (σ X0)
       grind)
    | exact superpose eq6576 eq20
    | (have j1 := eq6576 X1 X1
       grind)
    | exact resolve eq20 eq6576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq10896 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k (M.op X1 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq6576 X1 (τ X0)
       grind)
    | exact superpose eq6576 eq16
    | (have j1 := eq6576 X1 X1
       grind)
    | exact resolve eq16 eq6576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq6576
  have eq29093 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1253 (τ X1) (τ X0)
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq1253
    | exact resolve eq1253 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29273 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29093 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq29093
    | (have j0 := eq29093 X0 X1
       grind)
    | exact resolve eq29093 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29093
  have eq29294 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29273 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29273
    | (have j0 := eq29273 X0 X1
       grind)
    | exact resolve eq29273 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29273
  have eq29297 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (M.op X0 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29294 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq29294
    | (have j0 := eq29294 X0 X1
       grind)
    | exact resolve eq29294 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29294
  have eq29298 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29297 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29297
    | (have j0 := eq29297 X0 X1
       grind)
    | exact resolve eq29297 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29297
  have eq29873 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ (k X0 X1))) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29298 (τ X1) (τ X0)
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq29298
    | exact resolve eq29298 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq29298
  have eq45844 : ∀ X0 : G, (k (τ X0) (σ (M.op (τ (τ X0)) (τ (τ X0))))) = (τ (M.op X0 X0)) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10892 (σ (M.op (τ (τ X0)) (τ (τ X0)))) X0
       have i₂ := eq3539 X0
       grind)
    | exact superpose eq3539 eq10892
    | (have j0 := eq10892 X0 X0
       grind)
    | exact resolve eq10892 eq3539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3539 eq10892
  have eq45942 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq45844 X0
       have i₂ := eq608 (τ X0)
       grind)
    | exact superpose eq608 eq45844
    | (have j0 := eq45844 X0
       grind)
    | exact resolve eq45844 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608 eq45844
  have eq46320 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq29873 (M.op X0 X0) X0
       have i₂ := eq45942 X0
       grind)
    | exact superpose eq45942 eq29873
    | (have j1 := eq45942 X0
       grind)
    | exact resolve eq29873 eq45942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29873 eq45942
  have eq46334 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq46320 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46320
  have eq46344 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46334 X0
       have i₂ := eq3698 X0
       grind)
    | exact superpose eq3698 eq46334
    | (have j0 := eq46334 X0
       grind)
    | exact resolve eq46334 eq3698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3698 eq46334
  have eq48740 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (τ (M.op (σ (σ X0)) (σ (σ X0))))) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10896 (τ (M.op (σ (σ X0)) (σ (σ X0)))) X0
       have i₂ := eq3537 X0
       grind)
    | exact superpose eq3537 eq10896
    | (have j0 := eq10896 X0 X0
       grind)
    | exact resolve eq10896 eq3537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3537 eq10896
  have eq48854 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq48740 X0
       have i₂ := eq609 (σ X0)
       grind)
    | exact superpose eq609 eq48740
    | (have j0 := eq48740 X0
       grind)
    | exact resolve eq48740 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609 eq48740
  have eq49020 : y = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq48854 y
       have i₂ := eq5655
       grind)
    | exact superpose eq5655 eq48854
    | exact resolve eq48854 eq5655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48854
  have eq50086 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1253 (M.op x y) y
       have i₂ := eq49020
       grind)
    | exact superpose eq49020 eq1253
    | exact resolve eq1253 eq49020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253 eq49020
  have eq50096 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq50086
  have eq50101 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq50096
       have i₂ := eq5749
       grind)
    | exact superpose eq5749 eq50096
    | exact resolve eq50096 eq5749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50096
  have eq58758 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq46344 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq46344
    | exact resolve eq46344 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46344
  have eq77130 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ X0))
       have i₂ := eq58758 X0
       grind)
    | exact superpose eq58758 eq10
    | (have j1 := eq58758 X0
       grind)
    | exact resolve eq10 eq58758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58758
  have eq77565 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ X0))
       have i₂ := eq77130 X0
       grind)
    | exact superpose eq77130 eq10
    | (have j1 := eq77130 X0
       grind)
    | exact resolve eq10 eq77130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77130
  have eq77895 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0) (σ X0)
       have i₂ := eq77565 X0
       grind)
    | exact superpose eq77565 eq22
    | (have j1 := eq77565 X0
       grind)
    | exact resolve eq22 eq77565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77565
  have eq80720 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq77895 y
       have i₂ := eq5655
       grind)
    | exact superpose eq5655 eq77895
    | (have j0 := eq77895 y
       grind)
    | exact resolve eq77895 eq5655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5655 eq77895
  have eq80928 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq22 (σ y) (σ (M.op x y))
       have i₂ := eq80720
       grind)
    | exact superpose eq80720 eq22
    | exact resolve eq22 eq80720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq80720
  have eq80946 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq80928
       have i₂ := eq5749
       grind)
    | exact superpose eq5749 eq80928
    | exact resolve eq80928 eq5749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5749 eq80928
  have eq83053 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq5651
       have i₂ := eq50101
       grind)
    | exact superpose eq50101 eq5651
    | exact resolve eq5651 eq50101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50101
  have eq83061 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq80946
       have i₂ := eq5651
       grind)
    | exact superpose eq5651 eq80946
    | exact resolve eq80946 eq5651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80946
  have eq83109 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5651
  have eq83112 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq83053
  have eq83130 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq83061
       have r₂ := eq83109
       grind)
    | exact resolve eq83061 eq83109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83061 eq83109
  have eq83138 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq83112
       have r₂ := eq14
       grind)
    | exact resolve eq83112 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83112
  have eq83151 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq83130
       have r₂ := eq14
       grind)
    | exact resolve eq83130 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83130
  have eq83170 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 (M.op x y) X0
       have i₂ := eq83138
       grind)
    | exact superpose eq83138 eq13
    | exact resolve eq13 eq83138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83190 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (σ (k (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq79 (M.op x y) x
       have i₂ := eq83138
       grind)
    | exact superpose eq83138 eq79
    | exact resolve eq79 eq83138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq83203 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ (σ (k (M.op x y) X0)) ∨ (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq485 X0 (M.op x y)
       have i₂ := eq83138
       grind)
    | exact superpose eq83138 eq485
    | exact resolve eq485 eq83138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq83315 : ∀ X0 : G, (σ y) ≠ (σ (k (M.op x y) X0)) ∨ (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq83203 X0
       have i₂ := eq83151
       grind)
    | exact superpose eq83151 eq83203
    | (have j0 := eq83203 X0
       grind)
    | exact resolve eq83203 eq83151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83151 eq83203
  have eq83337 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (σ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq83170 X0
       have i₂ := eq13 y X0
       grind)
    | exact superpose eq13 eq83170
    | exact resolve eq83170 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83170
  have eq83355 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq83315 X0
       have j1 := eq83190 X0
       grind)
    | (have r₁ := eq83315 X0
       have r₂ := eq83190 X0
       grind)
    | exact resolve eq83315 eq83190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83190 eq83315
  have eq83365 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq83355 X0
       have i₂ := eq83337 X0
       grind)
    | exact superpose eq83337 eq83355
    | exact resolve eq83355 eq83337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83337 eq83355
  have eq87688 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq83365 x
       grind)
    | exact superpose eq83365 eq14
    | exact resolve eq14 eq83365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83365
  have eq88175 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq87688
       have i₂ := eq5548
       grind)
    | exact superpose eq5548 eq87688
    | exact resolve eq87688 eq5548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5548 eq87688
  have eq88393 : False := by grind
  exact eq88393

/-- `Equation844`: `x = x ◇ ((y ◇ y) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pyy_pxy_Equation844 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law844 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law844.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X0 X2))) = X0 := by
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
  have eq22 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1) X0 (M.op (M.op X0 X0) x)
       have i₂ := eq8 (M.op X0 X0) X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq37 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
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
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq44 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
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
  have eq46 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq37 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq60 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 X1
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X0 X0)
       have i₂ := eq22 X0 X0
       grind)
    | exact superpose eq22 eq11
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq22 X0 X0
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq89 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq46 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq46 eq13
    | (have j1 := eq46 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq101 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (M.op X0 X0)
       have i₂ := eq66 X0 (τ X1)
       grind)
    | exact superpose eq66 eq15
    | exact resolve eq15 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq205 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq43 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq734 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq44 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq44
    | (have j0 := eq44 X0 X1
       grind)
    | exact resolve eq44 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq790 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq734 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq734
    | (have j0 := eq734 X0 X1
       grind)
    | exact resolve eq734 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq1205 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq101 X1 X1
       have i₂ := eq790 X0 X1
       grind)
    | exact superpose eq790 eq101
    | (have j1 := eq790 X2 X0
       grind)
    | exact resolve eq101 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq790
  have eq1248 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq205 (M.op X0 X0)
       have i₂ := eq66 X0 (M.op X0 X0)
       grind)
    | exact superpose eq66 eq205
    | (have j0 := eq205 (M.op X0 X0)
       grind)
    | exact resolve eq205 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq1261 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq205 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq205
    | (have j0 := eq205 (τ X0)
       grind)
    | exact resolve eq205 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq205
  have eq1272 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1248 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248
  have eq1276 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1261 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1261
    | (have j0 := eq1261 X0
       grind)
    | exact resolve eq1261 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261
  have eq1285 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1276 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1276
    | (have j0 := eq1276 X0
       grind)
    | exact resolve eq1276 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276
  have eq1661 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq60 (σ (M.op X0 X0)) X1
       have i₂ := eq1272 X0
       grind)
    | exact superpose eq1272 eq60
    | exact resolve eq60 eq1272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1272
  have eq1723 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq89 x y X0
       grind)
    | exact superpose eq89 eq14
    | (have j1 := eq89 X0 y X0
       grind)
    | exact resolve eq14 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq1785 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq1723 X0
       have j1 := eq1205 y X0 x
       grind)
    | (have r₁ := eq1723 X0
       have r₂ := eq1205 y x x
       grind)
    | exact resolve eq1723 eq1205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205 eq1723
  have eq1825 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq33 X0 (σ y)
       have i₂ := eq1785 (σ X0)
       grind)
    | exact superpose eq1785 eq33
    | exact resolve eq33 eq1785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq1785
  have eq1831 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq1825 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1825
    | exact resolve eq1825 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1825
  have eq1952 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1285 y
       have i₂ := eq1831 y
       grind)
    | exact superpose eq1831 eq1285
    | (have j0 := eq1285 y
       grind)
    | (have r₁ := eq1285 y
       have r₂ := eq1831 y
       grind)
    | exact resolve eq1285 eq1831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285 eq1831
  have eq1970 : y = (M.op y y) := by grind
  clear eq1952
  have eq2064 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq60 y X0
       have i₂ := eq1970
       grind)
    | exact superpose eq1970 eq60
    | exact resolve eq60 eq1970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq2812 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1661 y X0
       have i₂ := eq1970
       grind)
    | exact superpose eq1970 eq1661
    | exact resolve eq1661 eq1970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1661 eq1970
  have eq3010 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2812 (σ x)
       grind)
    | exact superpose eq2812 eq14
    | exact resolve eq14 eq2812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2812
  have eq3025 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq3010
       have i₂ := eq2064 x
       grind)
    | exact superpose eq2064 eq3010
    | exact resolve eq3010 eq2064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2064 eq3010
  have eq3026 : False := by grind
  exact eq3026

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation854 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law854 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
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
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq94 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq98 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq94 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq94 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq94 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq94 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq114 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq98 (σ X0) (σ X1)
       grind)
    | exact superpose eq98 eq13
    | exact resolve eq13 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq114 X0 X1
       have i₂ := eq98 X0 X1
       grind)
    | exact superpose eq98 eq114
    | exact resolve eq114 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq114
  have eq1334 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq121 x y
       grind)
    | exact superpose eq121 eq14
    | (have r₁ := eq14
       have r₂ := eq121 x y
       grind)
    | exact resolve eq14 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq1367 : False := by grind
  exact eq1367

/-- `Equation856`: `x = x ◇ ((y ◇ z) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation856 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law856 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law856.models_iff G M).mp hM
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
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq111 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq115 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq111 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq111 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq111 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq111 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq131 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq115 (σ X0) (σ X1)
       grind)
    | exact superpose eq115 eq13
    | exact resolve eq13 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq131 X0 X1
       have i₂ := eq115 X0 X1
       grind)
    | exact superpose eq115 eq131
    | exact resolve eq131 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq131
  have eq1401 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq138 x y
       grind)
    | exact superpose eq138 eq14
    | (have r₁ := eq14
       have r₂ := eq138 x y
       grind)
    | exact resolve eq14 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq1430 : False := by grind
  exact eq1430

/-- `Equation860`: `x = x ◇ ((y ◇ z) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation860 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law860 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law860.models_iff G M).mp hM
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
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq95 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq99 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq95 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq95 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq95 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq115 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq99 (σ X0) (σ X1)
       grind)
    | exact superpose eq99 eq13
    | exact resolve eq13 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq115 X0 X1
       have i₂ := eq99 X0 X1
       grind)
    | exact superpose eq99 eq115
    | exact resolve eq115 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq115
  have eq1061 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq122 x y
       grind)
    | exact superpose eq122 eq14
    | (have r₁ := eq14
       have r₂ := eq122 x y
       grind)
    | exact resolve eq14 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq1089 : False := by grind
  exact eq1089

/-- `Equation873`: `x = y ◇ ((x ◇ x) ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation873 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law873 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law873.models_iff G M).mp hM
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
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq115 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq119 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq115 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq115 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq115 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq115 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq138 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq119 (σ X0) (σ X1)
       grind)
    | exact superpose eq119 eq13
    | exact resolve eq13 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq138 X0 X1
       have i₂ := eq119 X0 X1
       grind)
    | exact superpose eq119 eq138
    | exact resolve eq138 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq138
  have eq1343 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq147 x y
       grind)
    | exact superpose eq147 eq14
    | (have r₁ := eq14
       have r₂ := eq147 x y
       grind)
    | exact resolve eq14 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq1370 : False := by grind
  exact eq1370
