import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4425`: `x ◇ (x ◇ y) = (z ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_x_x_pxy_Equation4425 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4425 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4425.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X2) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq13 X0 (k (M.op X0 X0) X1)
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
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
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
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
  clear eq40
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq45
    | exact resolve eq45 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq45 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq45
    | (have j0 := eq45 y
       grind)
    | exact resolve eq45 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq143 : ∀ X0 : G, (k (k x X0) x) = (τ (k (k (σ x) (σ X0)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq60
    | exact resolve eq60 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq175 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : (σ x) = (k (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq36 (M.op x x)
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq36
    | exact resolve eq36 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq178 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq38 (M.op sF0 sF0)
       have i₂ := eq175 sF0
       grind)
    | exact superpose eq175 eq38
    | exact resolve eq38 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq179 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq20 eq178
    | exact resolve eq178 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq181 : (σ x) = (k (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq176
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq176
    | exact resolve eq176 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq189 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq91 (M.op sF2 sF2)
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq91
    | exact resolve eq91 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq200 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq30 eq189
    | exact resolve eq189 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq207 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq108 (M.op sF3 sF3)
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq108
    | exact resolve eq108 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq218 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq32 eq207
    | exact resolve eq207 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq336 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq336 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq336
    | exact resolve eq336 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq604 : ∀ X0 : G, (τ (k (k (σ x) (σ y)) X0)) = (k (k x y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq99 eq427
    | exact resolve eq427 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq691 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq16 X2 X3 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq714 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq691 X2 X3 X4 (M.op X4 x)
       have i₂ := eq691 X4 x X0 X1
       grind)
    | (have i₁ := eq691 X2 X3 X4 (M.op X4 x)
       have i₂ := eq691 X0 X1 X4 x
       grind)
    | exact superpose eq691 eq691
    | exact resolve eq691 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq715 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (M.op X3 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq691 X1 X2 X3 (M.op X3 x)
       have i₂ := eq16 X3 x X0
       grind)
    | exact superpose eq16 eq691
    | exact resolve eq691 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq719 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq691 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq691
    | (have j0 := eq691 X0 X1 x y
       grind)
    | exact resolve eq691 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq720 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq691
    | (have j0 := eq691 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq691 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq727 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X4 X4) X4) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq16 X2 (M.op X2 x) X4
       have i₂ := eq691 X2 x X0 X1
       grind)
    | (have i₁ := eq16 X2 (M.op X2 x) X4
       have i₂ := eq691 X0 X1 X2 x
       grind)
    | exact superpose eq691 eq16
    | exact resolve eq16 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq728 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq719 x x
       have i₂ := eq720 x x
       grind)
    | (have i₁ := eq719 (σ x) (σ y)
       have i₂ := eq720 x x
       grind)
    | exact superpose eq720 eq719
    | (have j0 := eq719 (σ x) (σ y)
       have j1 := eq720 x y
       grind)
    | exact resolve eq719 eq720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq732 : ∀ X0 X3 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X3 (M.op (M.op X0 X0) X0)) := by
    intro X0 X3
    first
    | (have i₁ := eq715 X0 x x X3
       have i₂ := eq720 x x
       grind)
    | (have i₁ := eq715 X0 (σ x) (σ y) X3
       have i₂ := eq720 X0 x
       grind)
    | exact superpose eq720 eq715
    | (have j0 := eq715 X0 (σ x) (σ y) X3
       grind)
    | exact resolve eq715 eq720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq733 : ∀ X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq714 x x X2 X3 X4
       have i₂ := eq720 x x
       grind)
    | (have i₁ := eq714 (σ x) (σ y) X2 X3 X4
       have i₂ := eq720 x x
       grind)
    | exact superpose eq720 eq714
    | (have j0 := eq714 (σ x) (σ y) X2 X3 X4
       grind)
    | exact resolve eq714 eq720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq743 : ∀ X4 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X4 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X4
    first
    | (have i₁ := eq733 x x X4
       have i₂ := eq720 x x
       grind)
    | (have i₁ := eq733 (σ x) (σ y) X4
       have i₂ := eq720 x x
       grind)
    | exact superpose eq720 eq733
    | (have j0 := eq733 (σ x) (σ y) X4
       grind)
    | exact resolve eq733 eq720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq766 : ∀ X2 : G, (M.op (M.op X2 X2) X2) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X2
    first
    | (have i₁ := eq16 x x X2
       have i₂ := eq720 x x
       grind)
    | (have i₁ := eq16 (σ x) (σ y) X2
       have i₂ := eq720 x x
       grind)
    | exact superpose eq720 eq16
    | (have j0 := eq16 (σ x) (σ y) X2
       grind)
    | exact resolve eq16 eq720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq787 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq743 eq28
    | (have j0 := eq28 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq28 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq743 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq28 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq796 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have j0 := eq787 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq804 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq796 eq35
    | exact resolve eq35 eq796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq817 : ∀ X0 : G, (k X0 (σ (M.op (σ x) (M.op (σ x) (σ y))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq804 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq804
    | exact resolve eq804 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq838 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq28
    | (have j0 := eq28 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq28 X0 (M.op X0 X0)
       have r₂ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq840 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (k X0 X1)) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq720 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq720
    | (have j1 := eq11 X1 X1
       grind)
    | exact resolve eq720 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq854 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
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
  have eq860 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq867 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq868 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq867 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq879 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq838 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq902 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq879 X0 X1
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq879 X1 X1
       have r₂ := eq28 X1 X1
       grind)
    | (have r₁ := eq879 X1 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq879 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq957 : (σ (M.op (σ x) (M.op (σ x) (σ y)))) ≠ (σ (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq817 eq868
    | (have j0 := eq868 (σ (M.op (σ x) (M.op (σ x) (σ y))))
       grind)
    | (have r₁ := eq868 (σ (M.op (σ x) (M.op (σ x) (σ y))))
       have r₂ := eq817 (σ (M.op (σ x) (M.op (σ x) (σ y))))
       grind)
    | exact resolve eq868 eq817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq970 : (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by grind
  clear eq957
  have eq1134 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq902 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq902
    | (have j0 := eq902 (σ X0) X1
       grind)
    | exact resolve eq902 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1135 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq902 (τ X0) X1
       have i₂ := eq427 X0 X0
       grind)
    | exact superpose eq427 eq902
    | (have j0 := eq902 (τ X0) X1
       grind)
    | exact resolve eq902 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq2273 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq854
       grind)
    | exact superpose eq854 eq41
    | exact resolve eq41 eq854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2274 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2273
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2273
    | exact resolve eq2273 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2273
  have eq2276 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq2274
    | exact resolve eq2274 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2274
  have eq2375 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (k X1 (σ (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1134 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1134
    | (have j0 := eq1134 (σ X0) X1
       grind)
    | exact resolve eq1134 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19342 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y)))))) := by
    intro X0
    first
    | exact superpose eq970 eq732
    | exact resolve eq732 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19348 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq970 eq691
    | exact resolve eq691 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19354 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq970 eq19348
    | exact resolve eq19348 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19348
  have eq19358 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq970 eq19342
    | exact resolve eq19342 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970 eq19342
  have eq19370 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq19354 x x
       have i₂ := eq720 x x
       grind)
    | (have i₁ := eq19354 (σ x) (σ y)
       have i₂ := eq720 x x
       grind)
    | exact superpose eq720 eq19354
    | (have j0 := eq19354 (σ x) (σ y)
       grind)
    | exact resolve eq19354 eq720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19354
  have eq19409 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq19370 eq15
    | exact resolve eq15 eq19370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22242 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2276 eq860
    | exact resolve eq860 eq2276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2276
  have eq22249 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq22242
       have r₂ := eq27
       grind)
    | exact resolve eq22242 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22242
  have eq22256 : y = (k y (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22249 eq218
    | exact resolve eq218 eq22249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq22249
  have eq22289 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq22256
    | exact resolve eq22256 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22256
  have eq22300 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq22289
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq22289
       have r₂ := eq13 y y
       grind)
    | (have r₁ := eq22289
       have r₂ := eq13 x y
       grind)
    | exact resolve eq22289 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22289
  have eq22305 : x = (k x (τ (σ y))) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22300 eq200
    | exact resolve eq200 eq22300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq22300
  have eq22339 : x = (k x y) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq22305
    | exact resolve eq22305 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22305
  have eq22345 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq902 y x
       grind)
    | (have r₁ := eq22339
       have r₂ := eq902 y x
       grind)
    | exact resolve eq22339 eq902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22339
  have eq22348 : x = (k x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq22345
       have r₂ := eq13 x y
       grind)
    | exact resolve eq22345 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22345
  have eq22352 : y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq854
       have i₂ := eq22348
       grind)
    | exact superpose eq22348 eq854
    | exact resolve eq854 eq22348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq22354 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq22348
       grind)
    | exact superpose eq22348 eq41
    | exact resolve eq41 eq22348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq22355 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq22354
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22354
    | exact resolve eq22354 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22354
  have eq22365 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq22355 eq860
    | exact resolve eq860 eq22355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860
  have eq22379 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq28 X0 y
       have i₂ := eq22352
       grind)
    | exact superpose eq22352 eq28
    | (have j0 := eq28 X0 y
       grind)
    | (have r₁ := eq28 X0 y
       have r₂ := eq22352
       grind)
    | exact resolve eq28 eq22352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22380 : y = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq175 y
       have i₂ := eq22352
       grind)
    | exact superpose eq22352 eq175
    | exact resolve eq175 eq22352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq22393 : (M.op y y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq720 y y
       have i₂ := eq22352
       grind)
    | exact superpose eq22352 eq720
    | exact resolve eq720 eq22352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22395 : ∀ X0 : G, y = (M.op x x) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq22379 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22379
  have eq22398 : y = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22352 eq22393
    | exact resolve eq22393 eq22352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22352 eq22393
  have eq22490 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq22365 eq720
    | exact resolve eq720 eq22365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22495 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq22365 eq22490
    | exact resolve eq22490 eq22365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22365 eq22490
  have eq23134 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1134 y X0
       have i₂ := eq22380
       grind)
    | exact superpose eq22380 eq1134
    | (have j0 := eq1134 y X0
       grind)
    | exact resolve eq1134 eq22380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22380
  have eq23139 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq23134 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23134
  have eq23145 : ∀ X0 : G, y = (M.op x x) ∨ x = (M.op x y) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq23139 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23139
    | (have j0 := eq23139 X0
       grind)
    | exact resolve eq23139 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23139
  have eq23174 : ∀ X0 : G, (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq720 x x
       have i₂ := eq22395 X0
       grind)
    | exact superpose eq22395 eq720
    | (have j1 := eq22395 X0
       grind)
    | exact resolve eq720 eq22395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22395
  have eq23179 : ∀ X0 : G, (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq23174 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23174
    | (have j0 := eq23174 X0
       grind)
    | exact resolve eq23174 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23174
  have eq23255 : ∀ X0 : G, y = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq22398 eq19358
    | exact resolve eq19358 eq22398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19358
  have eq23256 : y = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22398 eq19370
    | exact resolve eq19370 eq22398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23271 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq23256
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23256
    | exact resolve eq23256 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23256
  have eq23272 : ∀ X0 : G, y = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq23255 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23255
    | (have j0 := eq23255 X0
       grind)
    | exact resolve eq23255 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23255
  have eq23326 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq23271 eq23272
    | exact resolve eq23272 eq23271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23272
  have eq23391 : y = (k x x) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq23271
       grind)
    | exact superpose eq23271 eq11
    | exact resolve eq11 eq23271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23395 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq720 x x
       have i₂ := eq23271
       grind)
    | exact superpose eq23271 eq720
    | exact resolve eq720 eq23271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23397 : y = (k x x) ∨ x = y ∨ x = (M.op x y) ∨ y = (σ y) := by grind
  clear eq23391
  have eq23400 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq23395
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23395
    | exact resolve eq23395 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23395
  have eq23425 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq23400 eq796
    | exact resolve eq796 eq23400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796
  have eq23480 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq23400 eq19370
    | exact resolve eq19370 eq23400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23400
  have eq23498 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq23480
    | exact resolve eq23480 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23480
  have eq26582 : (σ y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq22495 eq19409
    | exact resolve eq19409 eq22495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26591 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq22495 eq691
    | exact resolve eq691 eq22495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26595 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq26591
    | (have j0 := eq26591 X0 X1
       grind)
    | exact resolve eq26591 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26591
  have eq26599 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq32 eq26582
    | exact resolve eq26582 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26582
  have eq26650 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26595 x x
       have i₂ := eq720 x x
       grind)
    | (have i₁ := eq26595 (σ x) (σ y)
       have i₂ := eq720 x x
       grind)
    | exact superpose eq720 eq26595
    | (have j0 := eq26595 (σ x) (σ y)
       grind)
    | exact resolve eq26595 eq720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26595
  have eq26693 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22495 eq26650
    | exact resolve eq26650 eq22495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26650
  have eq26855 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq26599 eq720
    | exact resolve eq720 eq26599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26599
  have eq26860 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq26 eq26855
    | exact resolve eq26855 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26855
  have eq26880 : ∀ X0 : G, (σ y) ≠ X0 ∨ (σ x) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26693 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq26693
       grind)
    | exact resolve eq13 eq26693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26894 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26693 eq11
    | exact resolve eq11 eq26693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26898 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26693 eq720
    | exact resolve eq720 eq26693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26899 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26693 eq727
    | exact resolve eq727 eq26693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26900 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq26894
  have eq26902 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq26899
    | (have j0 := eq26899 X0 X1
       grind)
    | exact resolve eq26899 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26899
  have eq26903 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq26898
    | exact resolve eq26898 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26898
  have eq26914 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq26902 x X1
       have i₂ := eq766 x
       grind)
    | exact superpose eq766 eq26902
    | exact resolve eq26902 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26902
  have eq26919 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op X1 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq26903 eq26914
    | exact resolve eq26914 eq26903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26903 eq26914
  have eq26989 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq26860 eq19409
    | exact resolve eq19409 eq26860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19409 eq26860
  have eq31186 : ∀ X0 : G, (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq720 x x
       have i₂ := eq23145 X0
       grind)
    | exact superpose eq23145 eq720
    | (have j1 := eq23145 X0
       grind)
    | exact resolve eq720 eq23145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31187 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op X1 (M.op x y)) ∨ x = (M.op x y) ∨ (k X2 (σ y)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq727 x x X1 X0
       have i₂ := eq23145 X2
       grind)
    | exact superpose eq23145 eq727
    | (have j1 := eq23145 X2
       grind)
    | exact resolve eq727 eq23145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23145
  have eq31190 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op X1 (M.op x y)) ∨ x = (M.op x y) ∨ (k X2 (σ y)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31187 X0 X1 X2
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq31187
    | (have j0 := eq31187 X0 X1 X2
       grind)
    | exact resolve eq31187 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31187
  have eq31191 : ∀ X0 : G, (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq31186 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq31186
    | (have j0 := eq31186 X0
       grind)
    | exact resolve eq31186 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31186
  have eq31202 : ∀ X1 X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (M.op x y)) ∨ x = (M.op x y) ∨ (k X2 (σ y)) = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq31190 x X1 X2
       have i₂ := eq766 x
       grind)
    | exact superpose eq766 eq31190
    | (have j0 := eq31190 x X1 X2
       grind)
    | exact resolve eq31190 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31190
  have eq31207 : ∀ X1 X2 : G, (M.op x y) = (M.op X1 (M.op x y)) ∨ x = (M.op x y) ∨ (k X2 (σ y)) = X2 := by
    intro X1 X2
    first
    | exact superpose eq31191 eq31202
    | (have j0 := eq31202 X1 X2
       have j1 := eq31191 X2
       grind)
    | exact resolve eq31202 eq31191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31191 eq31202
  have eq31292 : ∀ X0 X1 : G, (k X0 (σ (M.op x y))) = X0 ∨ x = (M.op x y) ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq817 X0
       have i₂ := eq23179 (M.op sF2 sF4)
       grind)
    | exact superpose eq23179 eq817
    | (have j1 := eq23179 X1
       grind)
    | exact resolve eq817 eq23179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq31340 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq19370
       have i₂ := eq23179 (M.op sF2 sF4)
       grind)
    | exact superpose eq23179 eq19370
    | (have j1 := eq23179 X0
       grind)
    | exact resolve eq19370 eq23179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23179
  have eq31374 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq31340
    | (have j0 := eq31340 X0
       grind)
    | exact resolve eq31340 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31340
  have eq31399 : ∀ X0 X1 : G, (k X1 y) = X1 ∨ x = (M.op x y) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq20 eq31292
    | (have j0 := eq31292 X0 X1
       grind)
    | exact resolve eq31292 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31292
  have eq31416 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq23498 eq31374
    | exact resolve eq31374 eq23498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23498 eq31374
  have eq31430 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq31416 eq868
    | (have j0 := eq868 (σ y)
       grind)
    | (have r₁ := eq868 (σ y)
       have r₂ := eq31416 (σ y)
       grind)
    | exact resolve eq868 eq31416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31416
  have eq31516 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq31430
  have eq31675 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq31516 eq720
    | exact resolve eq720 eq31516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31680 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq31516 eq31675
    | exact resolve eq31675 eq31516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31516 eq31675
  have eq31913 : (σ y) = (σ (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq31680 eq19370
    | exact resolve eq19370 eq31680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19370
  have eq31931 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq31680 eq691
    | exact resolve eq691 eq31680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31933 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq31680 eq727
    | exact resolve eq727 eq31680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq31945 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq31933
    | (have j0 := eq31933 X0 X1
       grind)
    | exact resolve eq31933 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31933
  have eq31946 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq31931
    | (have j0 := eq31931 X0 X1
       grind)
    | exact resolve eq31931 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31931
  have eq32002 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X1
    first
    | (have i₁ := eq31945 x X1
       have i₂ := eq766 x
       grind)
    | exact superpose eq766 eq31945
    | exact resolve eq31945 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766 eq31945
  have eq32003 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq31946 x x
       have i₂ := eq720 x x
       grind)
    | (have i₁ := eq31946 (σ x) (σ y)
       have i₂ := eq720 x x
       grind)
    | exact superpose eq720 eq31946
    | (have j0 := eq31946 (σ x) (σ y)
       grind)
    | exact resolve eq31946 eq720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31946
  have eq32048 : ∀ X1 : G, (σ y) = (M.op X1 (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X1
    first
    | exact superpose eq31680 eq32002
    | exact resolve eq32002 eq31680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32002
  have eq32049 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq31680 eq32003
    | exact resolve eq32003 eq31680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31680 eq32003
  have eq32209 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq32049 eq27
    | exact resolve eq27 eq32049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32049
  have eq35755 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23326 eq26
    | (have j1 := eq23326 (σ x)
       grind)
    | exact resolve eq26 eq23326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23326
  have eq35841 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq720 x x
       have i₂ := eq35755
       grind)
    | exact superpose eq35755 eq720
    | exact resolve eq720 eq35755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35755
  have eq35846 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35841
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq35841
    | exact resolve eq35841 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35841
  have eq35956 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35846 eq26919
    | exact resolve eq26919 eq35846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35846
  have eq35964 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq35956
  have eq36651 : (M.op x y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  have eq47249 : ∀ X0 : G, y ≠ y ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq868 y
       have i₂ := eq31399 X0 y
       grind)
    | exact superpose eq31399 eq868
    | (have j0 := eq868 y
       have j1 := eq31399 X0 x
       grind)
    | (have r₁ := eq868 y
       have r₂ := eq31399 X0 y
       grind)
    | (have r₁ := eq868 (σ (M.op x y))
       have r₂ := eq31399 (σ (M.op x y)) x
       grind)
    | exact resolve eq868 eq31399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31399
  have eq47318 : ∀ X0 : G, y = (M.op y y) ∨ x = (M.op x y) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq47249 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47249
  have eq50418 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op y y)) ∨ x = (M.op x y) ∨ (k X1 (σ (M.op x y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq732 y X0
       have i₂ := eq47318 X1
       grind)
    | exact superpose eq47318 eq732
    | (have j1 := eq47318 X1
       grind)
    | exact resolve eq732 eq47318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50424 : ∀ X0 : G, (M.op y y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq720 y y
       have i₂ := eq47318 X0
       grind)
    | exact superpose eq47318 eq720
    | (have j1 := eq47318 X0
       grind)
    | exact resolve eq720 eq47318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50429 : ∀ X0 : G, y = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq47318 eq50424
    | (have j0 := eq50424 X0
       have j1 := eq47318 X0
       grind)
    | exact resolve eq50424 eq47318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50424
  have eq50434 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 y) ∨ x = (M.op x y) ∨ (k X1 (σ (M.op x y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq47318 eq50418
    | (have j0 := eq50418 X0 X1
       have j1 := eq47318 X1
       grind)
    | exact resolve eq50418 eq47318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47318 eq50418
  have eq50446 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ (k X1 (σ (M.op x y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq50429 eq50434
    | (have j0 := eq50434 X0 X1
       have j1 := eq50429 X1
       grind)
    | exact resolve eq50434 eq50429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50429 eq50434
  have eq52414 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq50446 x X0
       grind)
    | exact superpose eq50446 eq18
    | (have j1 := eq50446 x X0
       grind)
    | exact resolve eq18 eq50446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50446
  have eq52463 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq52414 eq868
    | (have j0 := eq868 (σ (M.op x y))
       grind)
    | (have r₁ := eq868 (σ (M.op x y))
       have r₂ := eq52414 (σ (M.op x y))
       grind)
    | exact resolve eq868 eq52414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52469 : ∀ X0 : G, (σ (σ (M.op x y))) ≠ (σ (σ (M.op x y))) ∨ (k X0 (σ (σ (M.op x y)))) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq52414 eq1134
    | (have j0 := eq1134 (σ (M.op x y)) X0
       grind)
    | exact resolve eq1134 eq52414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134 eq52414
  have eq52549 : ∀ X0 : G, (k X0 (σ (σ (M.op x y)))) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq52469 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52469
  have eq52552 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq52463
  have eq52692 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq52552 eq732
    | exact resolve eq732 eq52552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52698 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq52552 eq720
    | exact resolve eq720 eq52552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52706 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq52552 eq52698
    | exact resolve eq52698 eq52552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52698
  have eq52711 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq52552 eq52692
    | exact resolve eq52692 eq52552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52552 eq52692
  have eq52727 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq52706 eq52711
    | exact resolve eq52711 eq52706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52711
  have eq53064 : y = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq52706 eq22398
    | exact resolve eq22398 eq52706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53087 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq52706 eq26919
    | exact resolve eq26919 eq52706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53090 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq52706 eq32048
    | exact resolve eq32048 eq52706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53101 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq53090
  have eq53109 : y = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq53064
  have eq53131 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq53101
       have r₂ := eq32209
       grind)
    | exact resolve eq53101 eq32209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53101
  have eq53134 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq53087
       have r₂ := eq27
       grind)
    | exact resolve eq53087 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53087
  have eq53150 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23271 eq53109
    | exact resolve eq53109 eq23271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53109
  have eq53239 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq23271 eq53150
    | exact resolve eq53150 eq23271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23271 eq53150
  have eq53869 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq53131 eq52727
    | exact resolve eq52727 eq53131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52727
  have eq53915 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq53869 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53869
  have eq54245 : ∀ X0 : G, (σ (σ (M.op x y))) ≠ (σ (σ (M.op x y))) ∨ (k X0 (σ (σ (M.op x y)))) = X0 ∨ x = (M.op x y) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq23425 eq2375
    | (have j0 := eq2375 (M.op x y) X0
       grind)
    | exact resolve eq2375 eq23425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2375 eq23425
  have eq54322 : ∀ X0 : G, (k X0 (σ (σ (M.op x y)))) = X0 ∨ x = (M.op x y) ∨ y = (σ y) := by
    intro X0
    first
    | (have j0 := eq54245 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54245
  have eq54398 : ∀ X0 : G, (k X0 (σ (σ (M.op x y)))) = X0 ∨ x = (M.op x y) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq20 eq54322
    | (have j0 := eq54322 X0
       grind)
    | exact resolve eq54322 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54322
  have eq54458 : ∀ X0 : G, (k X0 (σ (σ (M.op x y)))) = X0 ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq52549 eq54398
    | (have j0 := eq54398 X0
       have j1 := eq52549 X0
       grind)
    | exact resolve eq54398 eq52549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52549 eq54398
  have eq54564 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq53915 eq728
    | exact resolve eq728 eq53915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53915
  have eq54716 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq54564 eq22398
    | exact resolve eq22398 eq54564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22398 eq54564
  have eq54754 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq54716
  have eq54879 : y = (k x x) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq54754
       grind)
    | exact superpose eq54754 eq11
    | exact resolve eq11 eq54754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54754
  have eq54885 : y = (k x x) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq54879
  have eq54990 : ∀ X0 : G, (τ (σ (σ (M.op x y)))) ≠ (τ (σ (σ (M.op x y)))) ∨ (k X0 (τ (σ (σ (M.op x y))))) = X0 ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq54458 eq1135
    | (have j0 := eq1135 (σ (σ (M.op x y))) X0
       grind)
    | exact resolve eq1135 eq54458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq55046 : (τ (σ (M.op x y))) = (k (M.op x y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq54458 eq51
    | exact resolve eq51 eq54458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq54458
  have eq55076 : ∀ X0 : G, (k X0 (τ (σ (σ (M.op x y))))) = X0 ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | (have j0 := eq54990 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54990
  have eq55108 : (M.op x y) = (k (M.op x y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq29 eq55046
    | exact resolve eq55046 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55046
  have eq55150 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq55076 X0
       have i₂ := eq15 sF1
       grind)
    | exact superpose eq15 eq55076
    | exact resolve eq55076 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55076
  have eq55229 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq55150 eq868
    | (have j0 := eq868 (σ (M.op x y))
       grind)
    | (have r₁ := eq868 (σ (M.op x y))
       have r₂ := eq55150 (σ (M.op x y))
       grind)
    | exact resolve eq868 eq55150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55150
  have eq55320 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by grind
  clear eq55229
  have eq55470 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq55320 eq720
    | exact resolve eq720 eq55320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55479 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq55320 eq55470
    | exact resolve eq55470 eq55320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55320 eq55470
  have eq55735 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35964 eq55479
    | exact resolve eq55479 eq35964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35964
  have eq55857 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq55479 eq26919
    | exact resolve eq26919 eq55479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26919
  have eq55860 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq55479 eq32048
    | exact resolve eq32048 eq55479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32048 eq55479
  have eq55871 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by grind
  clear eq55860
  have eq55892 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq55735
  have eq55901 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq55871
       have r₂ := eq32209
       grind)
    | exact resolve eq55871 eq32209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32209 eq55871
  have eq55904 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq55857
       have r₂ := eq27
       grind)
    | exact resolve eq55857 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55857
  have eq55974 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq55892
       have r₂ := eq36651
       grind)
    | exact resolve eq55892 eq36651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36651 eq55892
  have eq55993 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq55974
    | exact resolve eq55974 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55974
  have eq56002 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq55993
       have r₂ := eq27
       grind)
    | exact resolve eq55993 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55993
  have eq56087 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq55901 eq31913
    | exact resolve eq31913 eq55901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31913
  have eq56135 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq56087
  have eq56165 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq56135
    | exact resolve eq56135 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56135
  have eq56166 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq56165
  have eq56224 : (M.op x y) = (τ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq56166 eq29
    | exact resolve eq29 eq56166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq56258 : (M.op x y) = (k (M.op x y) (σ (M.op (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq56166 eq179
    | exact resolve eq179 eq56166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq58310 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq56258
       have i₂ := eq31207 x (M.op sF0 sF0)
       grind)
    | exact superpose eq31207 eq56258
    | (have j1 := eq31207 x X0
       grind)
    | exact resolve eq56258 eq31207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31207 eq56258
  have eq58325 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq58310 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58310
  have eq58339 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq58325
    | (have j0 := eq58325 X0
       grind)
    | exact resolve eq58325 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58325
  have eq58353 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq55108 eq58339
    | exact resolve eq58339 eq55108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55108 eq58339
  have eq58360 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq56166 eq58353
    | (have j0 := eq58353 (M.op x y)
       grind)
    | exact resolve eq58353 eq56166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58353
  have eq58363 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq58360 X0
       have j1 := eq902 (M.op x y) X0
       grind)
    | (have r₁ := eq58360 X0
       have r₂ := eq902 (M.op x y) x
       grind)
    | (have r₁ := eq58360 (M.op x y)
       have r₂ := eq902 (M.op x y) x
       grind)
    | exact resolve eq58360 eq902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902 eq58360
  have eq58369 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq58363 eq868
    | (have j0 := eq868 (M.op x y)
       grind)
    | (have r₁ := eq868 (M.op x y)
       have r₂ := eq58363 (M.op x y)
       grind)
    | exact resolve eq868 eq58363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58363
  have eq58443 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq58369
  have eq58615 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq58443 eq732
    | exact resolve eq732 eq58443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq58621 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq58443 eq720
    | exact resolve eq720 eq58443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq58627 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq58443 eq58621
    | exact resolve eq58621 eq58443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58621
  have eq58632 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq58443 eq58615
    | exact resolve eq58615 eq58443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58443 eq58615
  have eq58645 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq58627 eq58632
    | exact resolve eq58632 eq58627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58632
  have eq60606 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq53134 eq52706
    | exact resolve eq52706 eq53134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52706 eq53134
  have eq60616 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq60606
  have eq60633 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq60616
    | exact resolve eq60616 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60616
  have eq60702 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq60633
       have r₂ := eq27
       grind)
    | exact resolve eq60633 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60633
  have eq60774 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq60702 eq27
    | exact resolve eq27 eq60702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60863 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq60702 eq58627
    | exact resolve eq58627 eq60702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60702
  have eq60864 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq60863
  have eq60948 : (M.op x y) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq53131 eq60774
    | exact resolve eq60774 eq53131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53131 eq60774
  have eq61069 : (M.op x y) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq60864 eq11
    | exact resolve eq11 eq60864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60864
  have eq61075 : (M.op x y) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq61069
  have eq61082 : (M.op x y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq61075
       have r₂ := eq60948
       grind)
    | exact resolve eq61075 eq60948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60948 eq61075
  have eq61111 : (k x x) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq61082 eq98
    | exact resolve eq98 eq61082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61082
  have eq61138 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq56224 eq61111
    | exact resolve eq61111 eq56224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61111
  have eq62857 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq55904 eq56002
    | exact resolve eq56002 eq55904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56002
  have eq62860 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by grind
  clear eq55904
  have eq62863 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq62857
  have eq62883 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq62863
       have r₂ := eq62860
       grind)
    | exact resolve eq62863 eq62860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62860 eq62863
  have eq62963 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x y) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq62883 eq27
    | exact resolve eq27 eq62883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63052 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq62883 eq58627
    | exact resolve eq58627 eq62883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58627 eq62883
  have eq63053 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by grind
  clear eq63052
  have eq63139 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq55901 eq62963
    | exact resolve eq62963 eq55901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55901 eq62963
  have eq63230 : (M.op x y) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq63053 eq11
    | exact resolve eq11 eq63053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63053
  have eq63236 : (M.op x y) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by grind
  clear eq63230
  have eq63261 : (M.op x y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq63236
       have r₂ := eq63139
       grind)
    | exact resolve eq63236 eq63139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63139 eq63236
  have eq63287 : (k x x) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq63261 eq98
    | exact resolve eq98 eq63261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63261
  have eq63319 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq56224 eq63287
    | exact resolve eq63287 eq56224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56224 eq63287
  have eq94232 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq61138
       have i₂ := eq23397
       grind)
    | exact superpose eq23397 eq61138
    | exact resolve eq61138 eq23397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23397
  have eq94251 : y = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq94232
  have eq94279 : (σ y) = (σ (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq94251
       grind)
    | exact superpose eq94251 eq24
    | exact resolve eq24 eq94251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94312 : x = (k x (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq22348
       have i₂ := eq94251
       grind)
    | exact superpose eq94251 eq22348
    | exact resolve eq22348 eq94251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94342 : (M.op x y) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by grind
  have eq94449 : (τ (k (k (σ x) (σ y)) (σ x))) = (k (k x (σ y)) x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq94279 eq143
    | exact resolve eq143 eq94279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq94279
  have eq94578 : (k (k x y) (τ (σ x))) = (k (k x (σ y)) x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq604 eq94449
    | exact resolve eq94449 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604 eq94449
  have eq94664 : (k (k x y) x) = (k (k x (σ y)) x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq94578
    | exact resolve eq94578 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq94578
  have eq94718 : (k x x) = (k (k x (σ y)) x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq94664
       have i₂ := eq22348
       grind)
    | exact superpose eq22348 eq94664
    | exact resolve eq94664 eq22348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22348 eq94664
  have eq94746 : y = (k (k x (σ y)) x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq54885 eq94718
    | exact resolve eq94718 eq54885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54885 eq94718
  have eq94760 : (σ y) = (k (k x (σ y)) x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq94251 eq94746
    | exact resolve eq94746 eq94251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94251 eq94746
  have eq94766 : (σ y) = (k x x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq94312 eq94760
    | exact resolve eq94760 eq94312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94312 eq94760
  have eq94769 : (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq61138 eq94766
    | exact resolve eq94766 eq61138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61138 eq94766
  have eq94771 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq94769
       have r₂ := eq94342
       grind)
    | exact resolve eq94769 eq94342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94342 eq94769
  have eq94775 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq94771
       grind)
    | exact superpose eq94771 eq24
    | exact resolve eq24 eq94771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94771
  have eq94883 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq94775
    | exact resolve eq94775 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94775
  have eq94907 : (M.op x y) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq56166 eq94883
    | exact resolve eq94883 eq56166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94883
  have eq103366 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26900 eq98
    | exact resolve eq98 eq26900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq103397 : y = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq103366
    | exact resolve eq103366 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103366
  have eq110910 : ∀ X0 : G, x ≠ y ∨ (k X0 x) = X0 ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq28 X0 x
       have i₂ := eq53239
       grind)
    | exact superpose eq53239 eq28
    | (have j0 := eq28 X0 x
       grind)
    | exact resolve eq28 eq53239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq53239
  have eq110944 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | (have j0 := eq110910 X0
       grind)
    | (have r₁ := eq110910 X0
       have r₂ := eq94907
       grind)
    | exact resolve eq110910 eq94907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94907 eq110910
  have eq110964 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq56166 eq110944
    | (have j0 := eq110944 X0
       grind)
    | exact resolve eq110944 eq56166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110944
  have eq110965 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | (have j0 := eq110964 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110964
  have eq111893 : x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq63319
       have i₂ := eq110965 x
       grind)
    | exact superpose eq110965 eq63319
    | exact resolve eq63319 eq110965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63319 eq110965
  have eq111909 : (M.op x y) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq111893
  have eq111943 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq111909 eq26
    | exact resolve eq26 eq111909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111909
  have eq112232 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq58645 eq111943
    | exact resolve eq111943 eq58645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58645 eq111943
  have eq112646 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq112232 eq27
    | exact resolve eq27 eq112232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112232
  have eq112893 : x = (M.op x y) := by
    first
    | (have r₁ := eq112646
       have r₂ := eq56166
       grind)
    | exact resolve eq112646 eq56166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56166 eq112646
  have eq112955 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq112893
       grind)
    | exact superpose eq112893 eq18
    | exact resolve eq18 eq112893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112956 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq112893
       grind)
    | exact superpose eq112893 eq22
    | exact resolve eq22 eq112893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq112959 : (σ x) = (k (σ x) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq181
       have i₂ := eq112893
       grind)
    | exact superpose eq112893 eq181
    | exact resolve eq181 eq112893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq112978 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq728
       have i₂ := eq112893
       grind)
    | exact superpose eq112893 eq728
    | exact resolve eq728 eq112893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq113051 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq112956 eq20
    | exact resolve eq20 eq112956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113776 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq112955 eq691
    | exact resolve eq691 eq112955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq114121 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq112978 eq22495
    | exact resolve eq22495 eq112978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22495
  have eq132937 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq114121 eq113776
    | exact resolve eq113776 eq114121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114121
  have eq132944 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26 eq132937
    | exact resolve eq132937 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132937
  have eq134755 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq132944
  have eq140507 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq840 x x
       have i₂ := eq103397
       grind)
    | exact superpose eq103397 eq840
    | (have j0 := eq840 x x
       grind)
    | exact resolve eq840 eq103397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840 eq103397
  have eq140769 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq140507
  have eq140865 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq112978 eq140769
    | exact resolve eq140769 eq112978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112978 eq140769
  have eq141025 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq140865
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq140865
    | exact resolve eq140865 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq140865
  have eq141129 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq141025
       have i₂ := eq112893
       grind)
    | exact superpose eq112893 eq141025
    | exact resolve eq141025 eq112893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112893 eq141025
  have eq141130 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq141129
  have eq141428 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq141130 eq112959
    | exact resolve eq112959 eq141130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112959 eq141130
  have eq141517 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq141428
    | exact resolve eq141428 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141428
  have eq141531 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq113051 eq141517
    | exact resolve eq141517 eq113051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141517
  have eq141540 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq26880 (σ x)
       grind)
    | (have r₁ := eq141531
       have r₂ := eq26880 (σ x)
       grind)
    | (have r₁ := eq141531
       have r₂ := eq26880 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq141531 eq26880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26880 eq141531
  have eq141559 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq141540 eq26900
    | exact resolve eq26900 eq141540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26900
  have eq141574 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq141540 eq868
    | (have j0 := eq868 (σ x)
       grind)
    | (have r₁ := eq868 (σ x)
       have r₂ := eq141540
       grind)
    | exact resolve eq868 eq141540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868 eq141540
  have eq141594 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq141574
  have eq141596 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq141559
  have eq141711 : (σ y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq141596 eq26989
    | exact resolve eq26989 eq141596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26989 eq141596
  have eq141834 : (σ y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq141711
  have eq141851 : y = (σ y) ∨ (σ x) = (σ y) ∨ y = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq141834
    | exact resolve eq141834 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq141834
  have eq141852 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (σ y) := by grind
  clear eq141851
  have eq142280 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq141852 eq27
    | exact resolve eq27 eq141852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141852
  have eq142459 : (σ x) = (σ y) ∨ y = (σ y) := by
    first
    | (have r₁ := eq142280
       have r₂ := eq113051
       grind)
    | exact resolve eq142280 eq113051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142280
  have eq142517 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (σ y) := by
    first
    | exact superpose eq142459 eq26
    | exact resolve eq26 eq142459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142601 : (σ x) = (k (σ x) (σ x)) ∨ y = (σ y) := by
    first
    | exact superpose eq142459 eq22355
    | exact resolve eq22355 eq142459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22355 eq142459
  have eq143731 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq142517 eq11
    | exact resolve eq11 eq142517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142517
  have eq143737 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq143731
  have eq143754 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq142601 eq143737
    | exact resolve eq143737 eq142601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142601 eq143737
  have eq143755 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq143754
  have eq143808 : (σ (M.op x y)) ≠ (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq143755 eq27
    | exact resolve eq27 eq143755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143755
  have eq143975 : y = (σ y) := by
    first
    | (have r₁ := eq143808
       have r₂ := eq113051
       grind)
    | exact resolve eq143808 eq113051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143808
  have eq144041 : (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq24
       have i₂ := eq143975
       grind)
    | exact superpose eq143975 eq24
    | exact resolve eq24 eq143975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq144116 : (M.op x y) = (M.op (M.op x y) (σ y)) := by
    first
    | (have i₁ := eq112955
       have i₂ := eq143975
       grind)
    | exact superpose eq143975 eq112955
    | exact resolve eq112955 eq143975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112955 eq143975
  have eq155289 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq141594 eq113776
    | exact resolve eq113776 eq141594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141594
  have eq155312 : (σ y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26693 eq155289
    | exact resolve eq155289 eq26693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26693 eq155289
  have eq155331 : (σ y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq155312
       have r₂ := eq134755
       grind)
    | exact resolve eq155312 eq134755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134755 eq155312
  have eq155508 : (σ y) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq155331 eq113776
    | exact resolve eq113776 eq155331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113776 eq155331
  have eq155532 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq144116 eq155508
    | exact resolve eq155508 eq144116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155508
  have eq159332 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq155532 eq27
    | exact resolve eq27 eq155532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155532
  have eq159504 : (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq159332
       have r₂ := eq113051
       grind)
    | exact resolve eq159332 eq113051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113051 eq159332
  have eq159773 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq159504 eq144041
    | exact resolve eq144041 eq159504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144041 eq159504
  have eq160273 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq159773 eq112956
    | exact resolve eq112956 eq159773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112956
  have eq160274 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq159773 eq20
    | exact resolve eq20 eq159773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq159773
  have eq161294 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq160273 eq26
    | exact resolve eq26 eq160273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq160273
  have eq161823 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq144116 eq161294
    | exact resolve eq161294 eq144116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144116 eq161294
  have eq162501 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq161823 eq27
    | exact resolve eq27 eq161823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq161823
  have eq162749 : False := by grind
  exact eq162749

/-- `Equation4425`: `x ◇ (x ◇ y) = (z ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_y_pxx_y_pxy_Equation4425 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4425 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4425.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X2) := by
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
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq16 X2 X3 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq557 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq177 X2 X3 X4 (M.op X4 x)
       have i₂ := eq177 X4 x X0 X1
       grind)
    | (have i₁ := eq177 X2 X3 X4 (M.op X4 x)
       have i₂ := eq177 X0 X1 X4 x
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 X0 X1 x y
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq563 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq573 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq562 x x
       have i₂ := eq563 x x
       grind)
    | (have i₁ := eq562 (σ x) (σ y)
       have i₂ := eq563 x x
       grind)
    | exact superpose eq563 eq562
    | (have j0 := eq562 (σ x) (σ y)
       have j1 := eq563 x y
       grind)
    | exact resolve eq562 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq578 : ∀ X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq557 x x X2 X3 X4
       have i₂ := eq563 x x
       grind)
    | (have i₁ := eq557 (σ x) (σ y) X2 X3 X4
       have i₂ := eq563 x x
       grind)
    | exact superpose eq563 eq557
    | (have j0 := eq557 (σ x) (σ y) X2 X3 X4
       grind)
    | exact resolve eq557 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq588 : ∀ X4 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X4 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X4
    first
    | (have i₁ := eq578 x x X4
       have i₂ := eq563 x x
       grind)
    | (have i₁ := eq578 (σ x) (σ y) X4
       have i₂ := eq563 x x
       grind)
    | exact superpose eq563 eq578
    | (have j0 := eq578 (σ x) (σ y) X4
       grind)
    | exact resolve eq578 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq612 : ∀ X2 : G, (M.op (M.op X2 X2) X2) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X2
    first
    | (have i₁ := eq16 x x X2
       have i₂ := eq563 x x
       grind)
    | (have i₁ := eq16 (σ x) (σ y) X2
       have i₂ := eq563 x x
       grind)
    | exact superpose eq563 eq16
    | (have j0 := eq16 (σ x) (σ y) X2
       grind)
    | exact resolve eq16 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq633 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op X0 X0) = (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq588 eq13
    | (have j0 := eq13 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq13 x (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq588 x
       grind)
    | exact resolve eq13 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq641 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have j0 := eq633 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq665 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (k X0 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq563 X0 X0
       have i₂ := eq641 X0
       grind)
    | exact superpose eq641 eq563
    | exact resolve eq563 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq668 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) ≠ X0 ∨ (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq641 X0
       grind)
    | exact superpose eq641 eq13
    | exact resolve eq13 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq670 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq588 (M.op sF2 sF4)
       have i₂ := eq641 (M.op sF2 sF4)
       grind)
    | exact superpose eq641 eq588
    | exact resolve eq588 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq671 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | (have i₁ := eq612 X0
       have i₂ := eq641 X0
       grind)
    | exact superpose eq641 eq612
    | exact resolve eq612 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq804 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) ∨ (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 ∨ (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq641 X0
       grind)
    | exact superpose eq641 eq11
    | exact resolve eq11 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq816 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
  have eq818 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq869 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) ∨ (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have j0 := eq804 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq901 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq869 X0
       have j1 := eq668 X0
       grind)
    | (have r₁ := eq869 X0
       have r₂ := eq668 X0
       grind)
    | exact resolve eq869 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668 eq869
  have eq942 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq671 (M.op sF2 sF4)
       have i₂ := eq901 (M.op sF2 sF4)
       grind)
    | exact superpose eq901 eq671
    | exact resolve eq671 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq943 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq665 (M.op sF2 sF4)
       have i₂ := eq901 (M.op sF2 sF4)
       grind)
    | exact superpose eq901 eq665
    | exact resolve eq665 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq944 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq641 (M.op sF2 sF4)
       have i₂ := eq901 (M.op sF2 sF4)
       grind)
    | exact superpose eq901 eq641
    | exact resolve eq641 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq956 : ∀ X0 : G, (τ (k (σ X0) (M.op (σ x) (M.op (σ x) (σ y))))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq362 X0 (σ X0)
       have i₂ := eq901 (σ X0)
       grind)
    | (have i₁ := eq362 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       have i₂ := eq901 (σ X0)
       grind)
    | exact superpose eq901 eq362
    | exact resolve eq362 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq960 : ∀ X0 : G, (k X0 X0) = (τ (k (σ X0) (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq956 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq956
    | exact resolve eq956 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq973 : ∀ X0 : G, (k X0 X0) = (k X0 (τ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq960 X0
       have i₂ := eq362 X0 (M.op sF2 sF4)
       grind)
    | exact superpose eq362 eq960
    | exact resolve eq960 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq1030 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq942 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq942
    | exact resolve eq942 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq1048 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq943 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq943
    | exact resolve eq943 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1519 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq670 eq1030
    | exact resolve eq1030 eq670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030
  have eq1579 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ (M.op (σ x) (M.op (σ x) (σ y)))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1519
       have i₂ := eq641 (σ (M.op sF2 sF4))
       grind)
    | exact superpose eq641 eq1519
    | exact resolve eq1519 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641 eq1519
  have eq2418 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq816
       grind)
    | exact superpose eq816 eq40
    | exact resolve eq40 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq816
  have eq2419 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2418
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2418
    | exact resolve eq2418 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2418
  have eq2421 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq2419
    | exact resolve eq2419 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2419
  have eq2423 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2421
       have i₂ := eq944 x
       grind)
    | exact superpose eq944 eq2421
    | exact resolve eq2421 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2421
  have eq3210 : (τ (M.op (σ x) (M.op (σ x) (σ y)))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (τ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq1579 eq362
    | exact resolve eq362 eq1579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362 eq1579
  have eq3215 : (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq973 eq3210
    | exact resolve eq3210 eq973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973 eq3210
  have eq3218 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq670 eq3215
    | exact resolve eq3215 eq670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670 eq3215
  have eq3231 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3218 eq14
    | exact resolve eq14 eq3218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4659 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2423 eq818
    | exact resolve eq818 eq2423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818 eq2423
  have eq4668 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq4659
       have r₂ := eq27
       grind)
    | exact resolve eq4659 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4659
  have eq4673 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4668
       have i₂ := eq944 sF2
       grind)
    | exact superpose eq944 eq4668
    | exact resolve eq4668 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944 eq4668
  have eq4675 : (τ (σ y)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4673 eq97
    | exact resolve eq97 eq4673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq4673
  have eq4695 : y = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq4675
    | exact resolve eq4675 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4675
  have eq4696 : y = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4695
  have eq4707 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq943 x
       have i₂ := eq4696
       grind)
    | exact superpose eq4696 eq943
    | exact resolve eq943 eq4696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943
  have eq4711 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1048 x
       have i₂ := eq4696
       grind)
    | exact superpose eq4696 eq1048
    | exact resolve eq1048 eq4696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048 eq4696
  have eq4716 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4711
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4711
    | exact resolve eq4711 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4711
  have eq4718 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4707
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4707
    | exact resolve eq4707 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4707
  have eq4722 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4716
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4716
    | exact resolve eq4716 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4716
  have eq4726 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq4722
    | exact resolve eq4722 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4722
  have eq4728 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4718 eq4726
    | exact resolve eq4726 eq4718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4726
  have eq4895 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4728 eq588
    | exact resolve eq588 eq4728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq4940 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4728 eq3218
    | exact resolve eq3218 eq4728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4942 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq4945 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq4940
    | exact resolve eq4940 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4940
  have eq4990 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq4895
    | (have j0 := eq4895 X0
       grind)
    | exact resolve eq4895 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4895
  have eq4994 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4728 eq4945
    | exact resolve eq4945 eq4728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4945
  have eq5038 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4728 eq4990
    | exact resolve eq4990 eq4728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4728 eq4990
  have eq5040 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq4994
    | exact resolve eq4994 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4994
  have eq5144 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5040 eq27
    | exact resolve eq27 eq5040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5040
  have eq5391 : (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4718 eq3231
    | exact resolve eq3231 eq4718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4718
  have eq5406 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq5391
    | exact resolve eq5391 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5391
  have eq5579 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5406 eq3218
    | exact resolve eq3218 eq5406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3218
  have eq5587 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq5579
    | exact resolve eq5579 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5579
  have eq5637 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5406 eq5587
    | exact resolve eq5587 eq5406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5587
  have eq5684 : y = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq5637
    | exact resolve eq5637 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq5637
  have eq5721 : y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq5684
       have r₂ := eq5144
       grind)
    | exact resolve eq5684 eq5144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5144 eq5684
  have eq5747 : (M.op x y) = (M.op x (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq5721
       grind)
    | exact superpose eq5721 eq18
    | exact resolve eq18 eq5721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5758 : (M.op x y) ≠ (σ y) ∨ y = (M.op x y) := by grind
  clear eq5721
  have eq6556 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5038 eq5747
    | exact resolve eq5747 eq5038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5038 eq5747
  have eq6559 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq6556
  have eq6564 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq6559
       have r₂ := eq4942
       grind)
    | exact resolve eq6559 eq4942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4942 eq6559
  have eq6604 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6564 eq27
    | exact resolve eq27 eq6564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6655 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6564 eq5406
    | exact resolve eq5406 eq6564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5406 eq6564
  have eq6656 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq6655
  have eq6660 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq6656
       have r₂ := eq5758
       grind)
    | exact resolve eq6656 eq5758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5758 eq6656
  have eq6696 : y = (M.op x y) := by
    first
    | (have r₁ := eq6660
       have r₂ := eq6604
       grind)
    | exact resolve eq6660 eq6604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6604 eq6660
  have eq6722 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq6696
       grind)
    | exact superpose eq6696 eq18
    | exact resolve eq18 eq6696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq6723 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq6696
       grind)
    | exact superpose eq6696 eq24
    | exact resolve eq24 eq6696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq6696
  have eq6874 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq6722 eq573
    | exact resolve eq573 eq6722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573 eq6722
  have eq6948 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq6874 eq3231
    | exact resolve eq3231 eq6874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3231
  have eq6955 : (M.op x y) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq6874 eq563
    | exact resolve eq563 eq6874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563 eq6874
  have eq7073 : (M.op x y) = (σ y) := by
    first
    | exact superpose eq6948 eq6723
    | exact resolve eq6723 eq6948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6723
  have eq7074 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq6948 eq20
    | exact resolve eq20 eq6948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq6948
  have eq7123 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq7073 eq26
    | exact resolve eq26 eq7073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq7073
  have eq7168 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6955 eq7123
    | exact resolve eq7123 eq6955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6955 eq7123
  have eq7251 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq7168 eq27
    | exact resolve eq27 eq7168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq7168
  have eq7352 : False := by grind
  exact eq7352

/-- `Equation4426`: `x ◇ (x ◇ y) = (z ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation4426 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4426 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4426.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X3) := by
    intro X0 X1 X2 X3
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq13 X0 (k (M.op X0 X0) X1)
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq45
    | exact resolve eq45 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq175 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq91 (M.op sF2 sF2)
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq91
    | exact resolve eq91 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq200 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq30 eq189
    | exact resolve eq189 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq207 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq108 (M.op sF3 sF3)
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq108
    | exact resolve eq108 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq218 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq32 eq207
    | exact resolve eq207 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq690 : ∀ X0 X1 X4 X5 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X4 X4) X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq16 x x X4 X5
       have i₂ := eq16 x x X0 X1
       grind)
    | (have i₁ := eq16 (M.op x x) X1 x x
       have i₂ := eq16 X0 X1 x (M.op (M.op x x) X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 x x
       have i₂ := eq16 X2 X3 x x
       grind)
    | (have i₁ := eq16 X0 X1 X2 (M.op (M.op X2 X2) X1)
       have i₂ := eq16 (M.op X2 X2) X1 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq693 X2 X3 X4 (M.op X4 x)
       have i₂ := eq693 X4 x X0 X1
       grind)
    | (have i₁ := eq693 X2 X3 X4 (M.op X4 x)
       have i₂ := eq693 X0 X1 X4 x
       grind)
    | exact superpose eq693 eq693
    | exact resolve eq693 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq693 X2 X3 X4 (M.op X4 x)
       have i₂ := eq16 X4 x X0 X1
       grind)
    | (have i₁ := eq693 X0 X1 (M.op X2 X2) X3
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq693
    | exact resolve eq693 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq746 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq693 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq693
    | (have j0 := eq693 X0 X1 x y
       grind)
    | exact resolve eq693 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq747 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq693
    | (have j0 := eq693 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq693 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq760 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 X4) X5) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 X2 (M.op X2 x) X4 X5
       have i₂ := eq693 X2 x X0 X1
       grind)
    | (have i₁ := eq16 X2 (M.op X2 x) X4 X5
       have i₂ := eq693 X0 X1 X2 x
       grind)
    | exact superpose eq693 eq16
    | exact resolve eq16 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq764 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq746 x x
       have i₂ := eq747 x x
       grind)
    | (have i₁ := eq746 (σ x) (σ y)
       have i₂ := eq747 x x
       grind)
    | exact superpose eq747 eq746
    | (have j0 := eq746 (σ x) (σ y)
       have j1 := eq747 x y
       grind)
    | exact resolve eq746 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq765 : ∀ X0 X1 X4 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X4 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq742 X0 X1 x x X4
       have i₂ := eq747 x x
       grind)
    | (have i₁ := eq742 X0 X1 (σ x) (σ y) X4
       have i₂ := eq747 X0 X1
       grind)
    | exact superpose eq747 eq742
    | (have j0 := eq742 X0 X1 (σ x) (σ y) X4
       grind)
    | exact resolve eq742 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq766 : ∀ X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq741 x x X2 X3 X4
       have i₂ := eq747 x x
       grind)
    | (have i₁ := eq741 (σ x) (σ y) X2 X3 X4
       have i₂ := eq747 x x
       grind)
    | exact superpose eq747 eq741
    | (have j0 := eq741 (σ x) (σ y) X2 X3 X4
       grind)
    | exact resolve eq741 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq772 : ∀ X4 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X4 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X4
    first
    | (have i₁ := eq766 x x X4
       have i₂ := eq747 x x
       grind)
    | (have i₁ := eq766 (σ x) (σ y) X4
       have i₂ := eq747 x x
       grind)
    | exact superpose eq747 eq766
    | (have j0 := eq766 (σ x) (σ y) X4
       grind)
    | exact resolve eq766 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq802 : ∀ X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X2 X3
    first
    | (have i₁ := eq690 x (M.op (M.op x x) x) X2 X3
       have i₂ := eq747 (M.op x x) x
       grind)
    | exact superpose eq747 eq690
    | exact resolve eq690 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq818 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq772 eq16
    | exact resolve eq16 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq820 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq772 eq28
    | (have j0 := eq28 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq28 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq772 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq28 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq829 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have j0 := eq820 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820
  have eq833 : ∀ X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) X2) := by
    intro X2
    first
    | (have i₁ := eq818 x x X2
       have i₂ := eq747 x x
       grind)
    | (have i₁ := eq818 (σ x) (σ y) X2
       have i₂ := eq747 x x
       grind)
    | exact superpose eq747 eq818
    | (have j0 := eq818 (σ x) (σ y) X2
       grind)
    | exact resolve eq818 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq837 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq829 eq35
    | exact resolve eq35 eq829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq850 : ∀ X0 : G, (k X0 (σ (M.op (σ x) (M.op (σ x) (σ y))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq837 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq837
    | exact resolve eq837 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq871 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq28
    | (have j0 := eq28 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq28 X0 (M.op X0 X0)
       have r₂ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq887 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
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
  have eq893 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq900 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq901 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq900 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq912 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq871 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq936 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq912 X0 X1
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq912 X1 X1
       have r₂ := eq28 X1 X1
       grind)
    | (have r₁ := eq912 X1 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq912 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq1000 : (σ (M.op (σ x) (M.op (σ x) (σ y)))) ≠ (σ (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq850 eq901
    | (have j0 := eq901 (σ (M.op (σ x) (M.op (σ x) (σ y))))
       grind)
    | (have r₁ := eq901 (σ (M.op (σ x) (M.op (σ x) (σ y))))
       have r₂ := eq850 (σ (M.op (σ x) (M.op (σ x) (σ y))))
       grind)
    | exact resolve eq901 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq1013 : (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by grind
  clear eq1000
  have eq1237 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq936 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq936
    | (have j0 := eq936 (σ X0) X1
       grind)
    | exact resolve eq936 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2236 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq887
       grind)
    | exact superpose eq887 eq40
    | exact resolve eq40 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2237 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2236
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2236
    | exact resolve eq2236 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2236
  have eq2239 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq2237
    | exact resolve eq2237 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2237
  have eq21078 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq1013 eq802
    | exact resolve eq802 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21085 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq1013 eq693
    | exact resolve eq693 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21092 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op X2 (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y)))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1013 eq760
    | exact resolve eq760 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21095 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op X2 (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1013 eq21092
    | exact resolve eq21092 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21092
  have eq21100 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq1013 eq21085
    | exact resolve eq21085 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21085
  have eq21117 : ∀ X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X2 (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X2
    first
    | (have i₁ := eq21095 x x X2
       have i₂ := eq802 x x
       grind)
    | exact superpose eq802 eq21095
    | exact resolve eq21095 eq802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21095
  have eq21119 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq21100 x x
       have i₂ := eq747 x x
       grind)
    | (have i₁ := eq21100 (σ x) (σ y)
       have i₂ := eq747 x x
       grind)
    | exact superpose eq747 eq21100
    | (have j0 := eq21100 (σ x) (σ y)
       grind)
    | exact resolve eq21100 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21100
  have eq22236 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq21119 eq15
    | exact resolve eq15 eq21119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24940 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2239 eq893
    | exact resolve eq893 eq2239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24947 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq24940
       have r₂ := eq27
       grind)
    | exact resolve eq24940 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24940
  have eq24954 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq24947 eq218
    | exact resolve eq218 eq24947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq24947
  have eq25009 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq24954
    | exact resolve eq24954 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24954
  have eq25018 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq25009
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq25009
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq25009
       have r₂ := eq13 y x
       grind)
    | exact resolve eq25009 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25009
  have eq25019 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) := by
    first
    | (have j1 := eq28 y x
       grind)
    | (have r₁ := eq25018
       have r₂ := eq28 x (σ x)
       grind)
    | (have r₁ := eq25018
       have r₂ := eq28 x x
       grind)
    | exact resolve eq25018 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25018
  have eq25021 : x = (k x (τ (σ x))) ∨ y = (k y x) := by
    first
    | exact superpose eq25019 eq200
    | exact resolve eq200 eq25019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq25019
  have eq25071 : x = (k x x) ∨ y = (k y x) := by
    first
    | exact superpose eq30 eq25021
    | exact resolve eq25021 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25021
  have eq25077 : y = (k y x) := by
    first
    | (have j1 := eq936 x y
       grind)
    | (have r₁ := eq25071
       have r₂ := eq936 x x
       grind)
    | exact resolve eq25071 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936 eq25071
  have eq25081 : x = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq887
       have i₂ := eq25077
       grind)
    | exact superpose eq25077 eq887
    | exact resolve eq887 eq25077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq25083 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq25077
       grind)
    | exact superpose eq25077 eq40
    | exact resolve eq40 eq25077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq25077
  have eq25084 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq25083
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25083
    | exact resolve eq25083 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25083
  have eq25091 : x = (M.op y y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq25084 eq2239
    | exact resolve eq2239 eq25084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2239
  have eq25094 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25084 eq893
    | exact resolve eq893 eq25084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893 eq25084
  have eq25487 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op x X0) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq802 y X0
       have i₂ := eq25081
       grind)
    | exact superpose eq25081 eq802
    | exact resolve eq802 eq25081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25081
  have eq25556 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op x X0) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq802 y X0
       have i₂ := eq25091
       grind)
    | exact superpose eq25091 eq802
    | exact resolve eq802 eq25091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25091
  have eq25625 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq25094 eq802
    | exact resolve eq802 eq25094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25094
  have eq28196 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq25487 y
       grind)
    | (have i₁ := eq18
       have i₂ := eq25487 x
       grind)
    | exact superpose eq25487 eq18
    | (have j1 := eq25487 y
       grind)
    | exact resolve eq18 eq25487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25487
  have eq28374 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28196 eq21119
    | exact resolve eq21119 eq28196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28375 : x = (M.op x x) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28196 eq22236
    | exact resolve eq22236 eq28196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28196
  have eq28406 : x = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq28374
    | exact resolve eq28374 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28374
  have eq28756 : (M.op x x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq747 x x
       have i₂ := eq28406
       grind)
    | exact superpose eq28406 eq747
    | exact resolve eq747 eq28406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28762 : x = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28406 eq28756
    | exact resolve eq28756 eq28406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28406 eq28756
  have eq28973 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28762 eq833
    | exact resolve eq833 eq28762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29046 : ∀ X0 : G, x = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28762 eq21078
    | exact resolve eq21078 eq28762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29049 : x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28762 eq21119
    | exact resolve eq21119 eq28762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28762
  have eq29084 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29049
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29049
    | exact resolve eq29049 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29049
  have eq29087 : ∀ X0 : G, x = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq29046 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29046
    | (have j0 := eq29046 X0
       grind)
    | exact resolve eq29046 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29046
  have eq29155 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29084 eq29087
    | exact resolve eq29087 eq29084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29087
  have eq29197 : (M.op x y) = (τ (M.op x y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29084 eq29
    | exact resolve eq29 eq29084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29974 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28973 y
       grind)
    | exact superpose eq28973 eq18
    | (have j1 := eq28973 y
       grind)
    | exact resolve eq18 eq28973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28973
  have eq30084 : (M.op x y) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29974 eq29
    | exact resolve eq29 eq29974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29974
  have eq31308 : (σ x) = (σ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29155 eq21119
    | exact resolve eq21119 eq29155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29155
  have eq32154 : x = (k x x) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq175 x
       have i₂ := eq28375
       grind)
    | exact superpose eq28375 eq175
    | exact resolve eq175 eq28375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32175 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x x) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq693 X0 X1 x x
       have i₂ := eq28375
       grind)
    | exact superpose eq28375 eq693
    | exact resolve eq693 eq28375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32180 : (M.op x x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq747 x x
       have i₂ := eq28375
       grind)
    | exact superpose eq28375 eq747
    | exact resolve eq747 eq28375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32186 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30084 eq32180
    | exact resolve eq32180 eq30084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32180
  have eq32190 : (M.op x x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq32175 x x
       have i₂ := eq747 x x
       grind)
    | (have i₁ := eq32175 (σ x) (σ y)
       have i₂ := eq747 x x
       grind)
    | exact superpose eq747 eq32175
    | (have j0 := eq32175 (σ x) (σ y)
       grind)
    | exact resolve eq32175 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32175
  have eq32209 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30084 eq32154
    | exact resolve eq32154 eq30084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30084 eq32154
  have eq32216 : (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32186 eq32190
    | exact resolve eq32190 eq32186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32186 eq32190
  have eq32233 : x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28375 eq32216
    | exact resolve eq32216 eq28375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28375 eq32216
  have eq32246 : (σ x) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29197 eq32233
    | exact resolve eq32233 eq29197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29197 eq32233
  have eq32557 : (σ x) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32246 eq11
    | exact resolve eq11 eq32246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32246
  have eq32567 : (σ x) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq32557
  have eq32574 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32209 eq32567
    | exact resolve eq32567 eq32209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32209 eq32567
  have eq32575 : (M.op x y) = (τ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq32574
  have eq32624 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32575 eq14
    | exact resolve eq14 eq32575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32575
  have eq32673 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq32624
    | exact resolve eq32624 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32624
  have eq32849 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32673 eq31308
    | exact resolve eq31308 eq32673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31308 eq32673
  have eq32858 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq32849
  have eq32876 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq32858
    | exact resolve eq32858 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32858
  have eq32877 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq32876
  have eq54223 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq25556 y
       grind)
    | exact superpose eq25556 eq18
    | (have j1 := eq25556 y
       grind)
    | exact resolve eq18 eq25556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25556
  have eq55234 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq54223 eq829
    | exact resolve eq829 eq54223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54223
  have eq65188 : ∀ X0 X1 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (k X1 (M.op x y)) = X1 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 x
       have i₂ := eq55234 X1
       grind)
    | exact superpose eq55234 eq28
    | (have j0 := eq28 X0 x
       have j1 := eq55234 X1
       grind)
    | (have r₁ := eq28 X0 x
       have r₂ := eq55234 X0
       grind)
    | exact resolve eq28 eq55234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65189 : ∀ X0 : G, x = (k x x) ∨ (k X0 (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq175 x
       have i₂ := eq55234 X0
       grind)
    | exact superpose eq55234 eq175
    | (have j1 := eq55234 X0
       grind)
    | exact resolve eq175 eq55234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq65218 : ∀ X0 : G, (M.op x x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (k X0 (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq747 x x
       have i₂ := eq55234 X0
       grind)
    | exact superpose eq55234 eq747
    | (have j1 := eq55234 X0
       grind)
    | exact resolve eq747 eq55234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65220 : ∀ X0 X1 : G, (k X1 (M.op x y)) = X1 ∨ (k X0 x) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have j0 := eq65188 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65188
  have eq65224 : ∀ X0 : G, x = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (k X0 (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq55234 eq65218
    | (have j0 := eq65218 X0
       have j1 := eq55234 X0
       grind)
    | exact resolve eq65218 eq55234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55234 eq65218
  have eq70214 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (k X1 (M.op x y)) = X1 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq1237 x X0
       have i₂ := eq65189 X1
       grind)
    | exact superpose eq65189 eq1237
    | (have j0 := eq1237 x X0
       have j1 := eq65189 X1
       grind)
    | exact resolve eq1237 eq65189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237 eq65189
  have eq70228 : ∀ X0 X1 : G, (k X0 (σ x)) = X0 ∨ (k X1 (M.op x y)) = X1 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have j0 := eq70214 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70214
  have eq70235 : ∀ X0 X1 : G, (k X1 (M.op x y)) = X1 ∨ (k X0 (σ x)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq70228 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq70228
    | (have j0 := eq70228 X0 X1
       grind)
    | exact resolve eq70228 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70228
  have eq70246 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (k X0 x) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq901 X0
       have i₂ := eq65220 (k X0 X0) x
       grind)
    | exact superpose eq65220 eq901
    | (have j0 := eq901 (M.op x y)
       have j1 := eq65220 X0 x
       grind)
    | (have r₁ := eq901 (M.op x y)
       have r₂ := eq65220 X0 (M.op x y)
       grind)
    | (have r₁ := eq901 x
       have r₂ := eq65220 x x
       grind)
    | exact resolve eq901 eq65220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65220
  have eq70322 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (k X0 x) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq70246 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70246
  have eq70509 : ∀ X0 X1 : G, x = (M.op x X0) ∨ (k X1 (M.op x y)) = X1 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq833 x
       have i₂ := eq65224 (M.op sF2 sF4)
       grind)
    | exact superpose eq65224 eq833
    | (have j1 := eq65224 X1
       grind)
    | exact resolve eq833 eq65224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70584 : ∀ X0 X1 : G, x = (M.op (σ x) X0) ∨ (k X1 (M.op x y)) = X1 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq21078 X0
       have i₂ := eq65224 (M.op sF2 sF4)
       grind)
    | exact superpose eq65224 eq21078
    | (have j1 := eq65224 X1
       grind)
    | exact resolve eq21078 eq65224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21078
  have eq70587 : ∀ X0 : G, x = (σ x) ∨ (k X0 (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq21119
       have i₂ := eq65224 (M.op sF2 sF4)
       grind)
    | exact superpose eq65224 eq21119
    | (have j1 := eq65224 X0
       grind)
    | exact resolve eq21119 eq65224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65224
  have eq70653 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq70587 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq70587
    | (have j0 := eq70587 X0
       grind)
    | exact resolve eq70587 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70587
  have eq70656 : ∀ X0 X1 : G, x = (M.op (σ x) X0) ∨ (k X1 (M.op x y)) = X1 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq70584 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq70584
    | (have j0 := eq70584 X0 X1
       grind)
    | exact resolve eq70584 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq70584
  have eq70724 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) X0) ∨ (k X1 (M.op x y)) = X1 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq70653 eq70656
    | (have j0 := eq70656 X0 X1
       have j1 := eq70653 X1
       grind)
    | exact resolve eq70656 eq70653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70656
  have eq70770 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq70653 eq901
    | (have j0 := eq901 (M.op x y)
       grind)
    | (have r₁ := eq901 (M.op x y)
       have r₂ := eq70653 (M.op x y)
       grind)
    | exact resolve eq901 eq70653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70653
  have eq70847 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq70770
  have eq71048 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op x y) X0) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq70847 eq802
    | exact resolve eq802 eq70847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71060 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq70847 eq747
    | exact resolve eq747 eq70847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71068 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq70847 eq71060
    | exact resolve eq71060 eq70847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70847 eq71060
  have eq74379 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq901 X0
       have i₂ := eq70235 (k X0 X0) x
       grind)
    | exact superpose eq70235 eq901
    | (have j0 := eq901 (M.op x y)
       have j1 := eq70235 X0 x
       grind)
    | (have r₁ := eq901 (M.op x y)
       have r₂ := eq70235 X0 (M.op x y)
       grind)
    | (have r₁ := eq901 (σ x)
       have r₂ := eq70235 (σ x) x
       grind)
    | exact resolve eq901 eq70235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70235
  have eq74455 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq74379 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74379
  have eq74776 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (k X0 x) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq747 X0 x
       have i₂ := eq70322 (M.op X0 x)
       grind)
    | exact superpose eq70322 eq747
    | (have j1 := eq70322 X0
       grind)
    | exact resolve eq747 eq70322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70322
  have eq74781 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (k X0 (σ x)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq71048 eq74776
    | (have j1 := eq71048 (M.op x y)
       grind)
    | exact resolve eq74776 eq71048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71048 eq74776
  have eq74821 : ∀ X0 : G, (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (k X0 (σ x)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq74455 eq74781
    | (have j0 := eq74781 X0
       have j1 := eq74455 X0
       grind)
    | exact resolve eq74781 eq74455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74455 eq74781
  have eq74902 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq70509 y X0
       grind)
    | exact superpose eq70509 eq18
    | (have j1 := eq70509 y X0
       grind)
    | exact resolve eq18 eq70509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70509
  have eq75057 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq74902 eq901
    | (have j0 := eq901 (M.op x y)
       grind)
    | (have r₁ := eq901 (M.op x y)
       have r₂ := eq74902 (M.op x y)
       grind)
    | exact resolve eq901 eq74902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74902
  have eq75134 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq75057
  have eq75342 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq75134 eq802
    | exact resolve eq802 eq75134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75134
  have eq78131 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq70724 X0 (M.op sF2 sF3)
       grind)
    | exact superpose eq70724 eq26
    | (have j1 := eq70724 (σ y) X0
       grind)
    | exact resolve eq26 eq70724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78534 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq78131 eq901
    | (have j0 := eq901 (M.op x y)
       grind)
    | (have r₁ := eq901 (M.op x y)
       have r₂ := eq78131 (M.op x y)
       grind)
    | exact resolve eq901 eq78131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78131
  have eq78610 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq78534
  have eq78843 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq78610 eq747
    | exact resolve eq747 eq78610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78849 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq78610 eq78843
    | exact resolve eq78843 eq78610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78610 eq78843
  have eq78905 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq78849 eq772
    | exact resolve eq772 eq78849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81564 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ (k X1 (σ x)) = X1 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq833 x
       have i₂ := eq74821 (M.op sF2 sF4)
       grind)
    | exact superpose eq74821 eq833
    | (have j1 := eq74821 X1
       grind)
    | exact resolve eq833 eq74821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74821
  have eq101574 : ∀ X0 X1 : G, (k X1 (M.op (σ x) X0)) = X1 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq25625 eq829
    | exact resolve eq829 eq25625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829 eq25625
  have eq102692 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq101574
    | (have j0 := eq101574 (σ y) X0
       grind)
    | exact resolve eq101574 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101574
  have eq103022 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq747 X0 x
       have i₂ := eq102692 (M.op X0 x)
       grind)
    | exact superpose eq102692 eq747
    | (have j1 := eq102692 X0
       grind)
    | exact resolve eq747 eq102692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103031 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq102692 eq103022
    | (have j0 := eq103022 X0
       have j1 := eq102692 X0
       grind)
    | exact resolve eq103022 eq102692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102692 eq103022
  have eq103291 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) X0) ∨ (k X1 (M.op (σ x) (σ y))) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq833 x
       have i₂ := eq103031 (M.op sF2 sF4)
       grind)
    | exact superpose eq103031 eq833
    | (have j1 := eq103031 X1
       grind)
    | exact resolve eq833 eq103031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833
  have eq103370 : ∀ X0 : G, (σ x) = (τ (σ x)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq22236
       have i₂ := eq103031 (M.op sF2 sF4)
       grind)
    | exact superpose eq103031 eq22236
    | (have j1 := eq103031 X0
       grind)
    | exact resolve eq22236 eq103031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22236 eq103031
  have eq103454 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq30 eq103370
    | (have j0 := eq103370 X0
       grind)
    | exact resolve eq103370 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq103370
  have eq103676 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq103454 eq901
    | (have j0 := eq901 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq901 (M.op (σ x) (σ y))
       have r₂ := eq103454 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq901 eq103454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103454
  have eq103744 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq103676
  have eq104385 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq103744 eq747
    | exact resolve eq747 eq103744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq104390 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq103744 eq104385
    | exact resolve eq104385 eq103744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103744 eq104385
  have eq104579 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq104390 eq71068
    | exact resolve eq71068 eq104390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104390
  have eq104619 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq104579
  have eq108921 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq104619 eq71068
    | exact resolve eq71068 eq104619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71068 eq104619
  have eq108937 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq108921
  have eq108961 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq108937
    | exact resolve eq108937 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108937
  have eq108962 : (σ (M.op x y)) = (σ y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq108961
  have eq109064 : (M.op x y) = (τ (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq108962 eq29
    | exact resolve eq29 eq108962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108962
  have eq109208 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq109064
    | exact resolve eq109064 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109064
  have eq109228 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq109208 eq27
    | exact resolve eq27 eq109208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109208
  have eq109498 : y = (M.op x y) ∨ x = (σ x) := by
    first
    | (have r₁ := eq109228
       have r₂ := eq29084
       grind)
    | exact resolve eq109228 eq29084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29084 eq109228
  have eq109564 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq109498
       grind)
    | exact superpose eq109498 eq18
    | exact resolve eq18 eq109498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109565 : (σ (M.op x y)) = (σ y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq24
       have i₂ := eq109498
       grind)
    | exact superpose eq109498 eq24
    | exact resolve eq24 eq109498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109498
  have eq109640 : (σ (M.op x y)) = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq20 eq109565
    | exact resolve eq109565 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109565
  have eq109641 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (σ x) := by
    first
    | exact superpose eq764 eq109564
    | exact resolve eq109564 eq764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109564
  have eq109867 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq109641 eq772
    | exact resolve eq772 eq109641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq109881 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (σ x) := by
    first
    | exact superpose eq109641 eq1013
    | exact resolve eq1013 eq109641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq109947 : ∀ X0 : G, (M.op x y) = (M.op X0 (σ (M.op x y))) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq109641 eq21117
    | exact resolve eq21117 eq109641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21117
  have eq109948 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq109641 eq21119
    | exact resolve eq21119 eq109641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109641
  have eq110023 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq20 eq109948
    | exact resolve eq109948 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109948
  have eq110024 : ∀ X0 : G, (M.op x y) = (M.op X0 (σ (M.op x y))) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq20 eq109947
    | (have j0 := eq109947 X0
       grind)
    | exact resolve eq109947 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109947
  have eq110086 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (σ x) := by
    first
    | exact superpose eq20 eq109881
    | exact resolve eq109881 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109881
  have eq110102 : ∀ X0 : G, (M.op x y) = (M.op X0 (σ y)) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq109640 eq110024
    | exact resolve eq110024 eq109640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110024
  have eq110147 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq109640 eq110086
    | exact resolve eq110086 eq109640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109640 eq110086
  have eq110167 : (M.op x y) = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq110102 eq110147
    | exact resolve eq110147 eq110102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110102 eq110147
  have eq110484 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq110167 eq26
    | exact resolve eq26 eq110167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110167
  have eq110684 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq109867 eq110484
    | exact resolve eq110484 eq109867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109867 eq110484
  have eq110911 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq110684 eq27
    | exact resolve eq27 eq110684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110684
  have eq111139 : x = (σ x) := by
    first
    | (have r₁ := eq110911
       have r₂ := eq110023
       grind)
    | exact resolve eq110911 eq110023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110023 eq110911
  have eq111181 : (M.op x y) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq111139
       grind)
    | exact superpose eq111139 eq18
    | exact resolve eq18 eq111139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq111204 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq764
       have i₂ := eq111139
       grind)
    | exact superpose eq111139 eq764
    | exact resolve eq764 eq111139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq112553 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (M.op x y) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq111181 eq70724
    | (have j0 := eq70724 X0 X0
       grind)
    | exact resolve eq70724 eq111181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112561 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq111181 eq693
    | exact resolve eq693 eq111181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq112788 : (M.op (σ x) (M.op x y)) = (σ (M.op (σ x) (M.op x y))) := by
    first
    | exact superpose eq111204 eq21119
    | exact resolve eq21119 eq111204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21119
  have eq112820 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq111204 eq75342
    | exact resolve eq75342 eq111204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75342
  have eq112858 : ∀ X0 : G, (M.op x y) = (σ x) ∨ (M.op (M.op x y) X0) = (M.op (σ x) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq112820 X0
       have i₂ := eq111139
       grind)
    | exact superpose eq111139 eq112820
    | (have j0 := eq112820 X0
       grind)
    | exact resolve eq112820 eq111139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111139 eq112820
  have eq119174 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op x y)) ∨ (k X1 (σ x)) = X1 ∨ (σ (M.op x y)) = (σ y) := by
    intro X1
    first
    | (have i₁ := eq112561 x X1
       have i₂ := eq81564 x (M.op x X1)
       grind)
    | exact superpose eq81564 eq112561
    | (have j1 := eq81564 x X1
       grind)
    | exact resolve eq112561 eq81564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81564
  have eq119525 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op x y)) ∨ (k X1 (M.op x y)) = X1 ∨ (σ (M.op x y)) = (σ y) := by
    intro X1
    first
    | exact superpose eq112858 eq119174
    | (have j1 := eq112858 (M.op x y)
       grind)
    | exact resolve eq119174 eq112858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112858 eq119174
  have eq119623 : ∀ X1 : G, (σ x) = (M.op (M.op x y) (M.op x y)) ∨ (k X1 (M.op x y)) = X1 ∨ (σ (M.op x y)) = (σ y) := by
    intro X1
    first
    | exact superpose eq70724 eq119525
    | (have j0 := eq119525 X1
       have j1 := eq70724 x X1
       grind)
    | exact resolve eq119525 eq70724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70724 eq119525
  have eq119657 : ∀ X1 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (k X1 (M.op x y)) = X1 ∨ (σ (M.op x y)) = (σ y) := by
    intro X1
    first
    | exact superpose eq112553 eq119623
    | (have j0 := eq119623 X1
       have j1 := eq112553 X1
       grind)
    | exact resolve eq119623 eq112553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112553 eq119623
  have eq119663 : ∀ X1 : G, (k X1 (M.op x y)) = X1 ∨ (σ (M.op x y)) = (σ y) := by
    intro X1
    first
    | (have j0 := eq119657 X1
       have j1 := eq28 X1 (M.op x y)
       grind)
    | (have r₁ := eq119657 X1
       have r₂ := eq28 x (M.op x y)
       grind)
    | exact resolve eq119657 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq119657
  have eq119673 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq119663 eq901
    | (have j0 := eq901 (M.op x y)
       grind)
    | (have r₁ := eq901 (M.op x y)
       have r₂ := eq119663 (M.op x y)
       grind)
    | exact resolve eq901 eq119663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119663
  have eq119758 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq119673
  have eq120293 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op (M.op x y) X1)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq119758 eq765
    | exact resolve eq765 eq119758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq120294 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op x y) X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq119758 eq802
    | exact resolve eq802 eq119758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120308 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq119758 eq112561
    | exact resolve eq112561 eq119758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120331 : (M.op x y) = (M.op (σ x) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq119758 eq120308
    | exact resolve eq120308 eq119758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119758 eq120308
  have eq120343 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq111204 eq120294
    | exact resolve eq120294 eq111204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120294
  have eq120344 : ∀ X0 X1 : G, (M.op (σ x) (M.op x y)) = (M.op X0 (M.op (M.op x y) X1)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq111204 eq120293
    | exact resolve eq120293 eq111204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120293
  have eq120386 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq120331 eq120343
    | exact resolve eq120343 eq120331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120343
  have eq120387 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op (M.op x y) X1)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq120331 eq120344
    | exact resolve eq120344 eq120331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120344
  have eq120423 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq120386 eq120387
    | exact resolve eq120387 eq120386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120386 eq120387
  have eq131371 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq111181
       have i₂ := eq103291 X0 (M.op sF2 y)
       grind)
    | exact superpose eq103291 eq111181
    | (have j1 := eq103291 X0 X0
       grind)
    | exact resolve eq111181 eq103291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131407 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq103291 X0 (M.op sF2 sF3)
       grind)
    | exact superpose eq103291 eq26
    | (have j1 := eq103291 (σ y) X0
       grind)
    | exact resolve eq26 eq103291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103291
  have eq131911 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq131407 eq901
    | (have j0 := eq901 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq901 (M.op (σ x) (σ y))
       have r₂ := eq131407 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq901 eq131407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131407
  have eq131981 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq131911
  have eq132114 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq131981 eq760
    | exact resolve eq760 eq131981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760
  have eq132115 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq131981 eq112561
    | exact resolve eq112561 eq131981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132120 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq131981 eq132115
    | exact resolve eq132115 eq131981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132115
  have eq132121 : ∀ X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | (have i₁ := eq132114 x x X2
       have i₂ := eq802 x x
       grind)
    | exact superpose eq802 eq132114
    | exact resolve eq132114 eq802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802 eq132114
  have eq132149 : ∀ X2 : G, (M.op (σ x) (M.op x y)) = (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq111204 eq132121
    | exact resolve eq132121 eq111204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132121
  have eq132168 : ∀ X2 : G, (M.op (σ x) (M.op x y)) = (M.op X2 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq131981 eq132149
    | exact resolve eq132149 eq131981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131981 eq132149
  have eq132179 : ∀ X2 : G, (M.op (σ x) (σ y)) = (M.op X2 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq132120 eq132168
    | exact resolve eq132168 eq132120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132120 eq132168
  have eq133303 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq132179 eq78849
    | exact resolve eq78849 eq132179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78849 eq132179
  have eq133338 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq133303
  have eq135005 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq131371 eq901
    | (have j0 := eq901 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq901 (M.op (σ x) (σ y))
       have r₂ := eq131371 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq901 eq131371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901 eq131371
  have eq135075 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq135005
  have eq135364 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq135075 eq112561
    | exact resolve eq112561 eq135075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112561
  have eq135369 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq135075 eq135364
    | exact resolve eq135364 eq135075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135075 eq135364
  have eq135524 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq135369 eq120423
    | exact resolve eq120423 eq135369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120423 eq135369
  have eq138309 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq133338 eq111204
    | exact resolve eq111204 eq133338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133338
  have eq138330 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq138309
    | exact resolve eq138309 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138309
  have eq138428 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq78905 eq138330
    | exact resolve eq138330 eq78905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78905 eq138330
  have eq138429 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq138428
  have eq138683 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq138429
  have eq142065 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq135524 eq111204
    | exact resolve eq111204 eq135524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111204 eq135524
  have eq142095 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq142065
       have r₂ := eq138683
       grind)
    | exact resolve eq142065 eq138683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138683 eq142065
  have eq142194 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq142095
    | exact resolve eq142095 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142095
  have eq142295 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq120331 eq142194
    | exact resolve eq142194 eq120331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120331 eq142194
  have eq142296 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq142295
  have eq142386 : (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq142296 eq29
    | exact resolve eq29 eq142296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq142296
  have eq142561 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq142386
    | exact resolve eq142386 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq142386
  have eq142628 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq142561 eq27
    | exact resolve eq27 eq142561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142561
  have eq142902 : y = (M.op x y) := by
    first
    | (have r₁ := eq142628
       have r₂ := eq32877
       grind)
    | exact resolve eq142628 eq32877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32877 eq142628
  have eq142959 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq142902
       grind)
    | exact superpose eq142902 eq24
    | exact resolve eq24 eq142902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq143011 : (M.op x y) = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq111181
       have i₂ := eq142902
       grind)
    | exact superpose eq142902 eq111181
    | exact resolve eq111181 eq142902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111181 eq142902
  have eq143898 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq143011 eq112788
    | exact resolve eq112788 eq143011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112788
  have eq143950 : (M.op x y) = (σ y) := by
    first
    | exact superpose eq143898 eq142959
    | exact resolve eq142959 eq143898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142959
  have eq143951 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq143898 eq20
    | exact resolve eq20 eq143898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq143898
  have eq144848 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq143950 eq26
    | exact resolve eq26 eq143950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq143950
  have eq145086 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq143011 eq144848
    | exact resolve eq144848 eq143011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143011 eq144848
  have eq145700 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq145086 eq27
    | exact resolve eq27 eq145086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq145086
  have eq145935 : False := by grind
  exact eq145935

/-- `Equation4426`: `x ◇ (x ◇ y) = (z ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxx_y_pxy_Equation4426 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4426 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4426.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
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
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X3) := by
    intro X0 X1 X2 X3
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
  have eq176 : ∀ X0 X1 X4 X5 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X4 X4) X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq16 x x X4 X5
       have i₂ := eq16 x x X0 X1
       grind)
    | (have i₁ := eq16 (M.op x x) X1 x x
       have i₂ := eq16 X0 X1 x (M.op (M.op x x) X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 x x
       have i₂ := eq16 X2 X3 x x
       grind)
    | (have i₁ := eq16 X0 X1 X2 (M.op (M.op X2 X2) X1)
       have i₂ := eq16 (M.op X2 X2) X1 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq556 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op X0 X0) X1) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq16 X2 X3 (M.op x x) X5
       have i₂ := eq176 x (M.op x x) X0 X1
       grind)
    | (have i₁ := eq16 X2 X3 (M.op x x) X5
       have i₂ := eq176 X0 X1 x (M.op x x)
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq179 X2 X3 X4 (M.op X4 x)
       have i₂ := eq179 X4 x X0 X1
       grind)
    | (have i₁ := eq179 X2 X3 X4 (M.op X4 x)
       have i₂ := eq179 X0 X1 X4 x
       grind)
    | exact superpose eq179 eq179
    | exact resolve eq179 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq578 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq179
    | (have j0 := eq179 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq179 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq597 : ∀ X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq572 x x X2 X3 X4
       have i₂ := eq578 x x
       grind)
    | (have i₁ := eq572 (σ x) (σ y) X2 X3 X4
       have i₂ := eq578 x x
       grind)
    | exact superpose eq578 eq572
    | (have j0 := eq572 (σ x) (σ y) X2 X3 X4
       grind)
    | exact resolve eq572 eq578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq603 : ∀ X4 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X4 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X4
    first
    | (have i₁ := eq597 x x X4
       have i₂ := eq578 x x
       grind)
    | (have i₁ := eq597 (σ x) (σ y) X4
       have i₂ := eq578 x x
       grind)
    | exact superpose eq578 eq597
    | (have j0 := eq597 (σ x) (σ y) X4
       grind)
    | exact resolve eq597 eq578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq633 : ∀ X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X2 X3
    first
    | (have i₁ := eq176 x (M.op (M.op x x) x) X2 X3
       have i₂ := eq578 (M.op x x) x
       grind)
    | exact superpose eq578 eq176
    | exact resolve eq176 eq578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq653 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op X0 X0) = (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq603 eq13
    | (have j0 := eq13 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq13 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq603 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq13 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have j0 := eq653 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq711 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op X0 X0) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq633 X0 (M.op X0 X0)
       have i₂ := eq658 (M.op X0 X0)
       grind)
    | exact superpose eq658 eq633
    | exact resolve eq633 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq715 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (M.op (σ x) (σ y))))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | exact superpose eq658 eq362
    | exact resolve eq362 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq922 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq923 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq922 X0
       have j1 := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq922 X0
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | exact resolve eq922 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq952 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq658 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq658
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq658 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq972 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq974 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq991 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq952 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952
  have eq3832 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq972
       grind)
    | exact superpose eq972 eq40
    | exact resolve eq40 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972
  have eq3833 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3832
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3832
    | exact resolve eq3832 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3832
  have eq3835 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq3833
    | exact resolve eq3833 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3833
  have eq18951 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq658 (M.op sF2 sF4)
       have i₂ := eq991 (M.op sF2 sF4)
       grind)
    | exact superpose eq991 eq658
    | (have j1 := eq991 X0
       grind)
    | exact resolve eq658 eq991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991
  have eq19070 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq18951 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq18951 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq18951 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18951
  have eq19205 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (k X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq633 X0 X1
       have i₂ := eq19070 X0
       grind)
    | exact superpose eq19070 eq633
    | exact resolve eq633 eq19070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19206 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq658 X0
       have i₂ := eq19070 X0
       grind)
    | exact superpose eq19070 eq658
    | exact resolve eq658 eq19070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq19207 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (k X0 X0) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq711 X0
       have i₂ := eq19070 X0
       grind)
    | exact superpose eq19070 eq711
    | exact resolve eq711 eq19070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq19225 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq578 X0 X0
       have i₂ := eq19070 X0
       grind)
    | exact superpose eq19070 eq578
    | exact resolve eq578 eq19070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19242 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq633 X0 (M.op X0 X0)
       have i₂ := eq19070 (M.op X0 X0)
       grind)
    | exact superpose eq19070 eq633
    | exact resolve eq633 eq19070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq19248 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (M.op (σ x) (σ y))))) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq715 X0
       have i₂ := eq19070 (σ X0)
       grind)
    | exact superpose eq19070 eq715
    | exact resolve eq715 eq19070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19264 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (M.op (σ x) (σ y))))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq19248 X0
       have i₂ := eq362 X0 (σ X0)
       grind)
    | exact superpose eq362 eq19248
    | exact resolve eq19248 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362 eq19248
  have eq19269 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq19242 X0
       have i₂ := eq19070 X0
       grind)
    | exact superpose eq19070 eq19242
    | exact resolve eq19242 eq19070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19242
  have eq19325 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (M.op (σ x) (σ y))))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq19264 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq19264
    | exact resolve eq19264 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19264
  have eq19384 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (k X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19205 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq19205
    | exact resolve eq19205 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19205
  have eq19551 : ∀ X0 : G, (k (σ X0) (M.op (σ x) (M.op (σ x) (σ y)))) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq19206 (σ X0)
       grind)
    | exact superpose eq19206 eq10
    | exact resolve eq10 eq19206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21193 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq19225 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq19225
    | exact resolve eq19225 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21743 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 (τ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq19206 X0
       have i₂ := eq19325 X0
       grind)
    | (have i₁ := eq19206 (τ (M.op (σ x) (M.op (σ x) (σ y))))
       have i₂ := eq19325 (τ (M.op (σ x) (M.op (σ x) (σ y))))
       grind)
    | exact superpose eq19325 eq19206
    | exact resolve eq19206 eq19325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19206 eq19325
  have eq22044 : ∀ X0 : G, (τ (M.op (σ x) (M.op (σ x) (σ y)))) = (k (k X0 X0) (τ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq715 (k X0 X0)
       have i₂ := eq19384 X0 (σ (k X0 X0))
       grind)
    | exact superpose eq19384 eq715
    | exact resolve eq715 eq19384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq22062 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ (k X0 X0)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq923 (σ (k X0 X0))
       have i₂ := eq19384 X0 (σ (k X0 X0))
       grind)
    | exact superpose eq19384 eq923
    | exact resolve eq923 eq19384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923 eq19384
  have eq22127 : ∀ X0 : G, (τ (M.op (σ x) (M.op (σ x) (σ y)))) = (k (k X0 X0) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq21743 eq22044
    | exact resolve eq22044 eq21743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21743 eq22044
  have eq22186 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq19207 eq22127
    | exact resolve eq22127 eq19207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19207 eq22127
  have eq22219 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq22186 eq14
    | exact resolve eq14 eq22186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22186
  have eq33348 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3835 eq974
    | exact resolve eq974 eq3835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974 eq3835
  have eq33355 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq33348
       have r₂ := eq27
       grind)
    | exact resolve eq33348 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33348
  have eq33361 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq33355
       have i₂ := eq19070 sF2
       grind)
    | exact superpose eq19070 eq33355
    | exact resolve eq33355 eq19070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33355
  have eq33365 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq33361
       have i₂ := eq19070 sF3
       grind)
    | exact superpose eq19070 eq33361
    | exact resolve eq33361 eq19070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33361
  have eq33369 : y = (k x x) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq33365
       have i₂ := eq19070 x
       grind)
    | exact superpose eq19070 eq33365
    | exact resolve eq33365 eq19070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33365
  have eq33371 : (σ y) = (k (σ y) (σ y)) ∨ y = (k x x) ∨ y = (k y y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq33369
       have i₂ := eq19070 y
       grind)
    | exact superpose eq19070 eq33369
    | exact resolve eq33369 eq19070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19070 eq33369
  have eq33570 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (k x x) ∨ y = (k y y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq33371 eq152
    | exact resolve eq152 eq33371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq33371
  have eq33620 : y = (k y y) ∨ y = (k x x) ∨ y = (k y y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq31 eq33570
    | exact resolve eq33570 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33570
  have eq33621 : (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) ∨ y = (k y y) := by grind
  clear eq33620
  have eq33645 : (τ (σ y)) = (k x x) ∨ y = (k x x) ∨ y = (k y y) := by
    first
    | exact superpose eq33621 eq97
    | exact resolve eq97 eq33621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq33621
  have eq33692 : y = (k x x) ∨ y = (k x x) ∨ y = (k y y) := by
    first
    | exact superpose eq31 eq33645
    | exact resolve eq33645 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq33645
  have eq33693 : y = (k y y) ∨ y = (k x x) := by grind
  clear eq33692
  have eq33715 : (σ y) = (k (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq33693
       grind)
    | exact superpose eq33693 eq40
    | exact resolve eq40 eq33693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33726 : (k y y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq19269 y
       have i₂ := eq33693
       grind)
    | exact superpose eq33693 eq19269
    | exact resolve eq19269 eq33693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19269
  have eq33732 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq22062 y
       have i₂ := eq33693
       grind)
    | exact superpose eq33693 eq22062
    | exact resolve eq22062 eq33693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22062
  have eq33751 : (σ (k y y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | exact superpose eq19551 eq33732
    | exact resolve eq33732 eq19551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19551 eq33732
  have eq33756 : y = (k x x) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq33693 eq33726
    | exact resolve eq33726 eq33693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33693 eq33726
  have eq33765 : (σ y) = (k (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq33715
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq33715
    | exact resolve eq33715 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33715
  have eq33774 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq33751
       have i₂ := eq40 y
       grind)
    | exact superpose eq40 eq33751
    | exact resolve eq33751 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq33751
  have eq33787 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq33774
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq33774
    | exact resolve eq33774 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33774
  have eq33795 : y = (k (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | exact superpose eq33756 eq33787
    | exact resolve eq33787 eq33756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33787
  have eq33803 : y = (k x x) ∨ y = (σ y) := by
    first
    | exact superpose eq33765 eq33795
    | exact resolve eq33795 eq33765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33765 eq33795
  have eq33825 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (σ y) := by
    first
    | (have i₁ := eq19225 x
       have i₂ := eq33803
       grind)
    | exact superpose eq33803 eq19225
    | exact resolve eq19225 eq33803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33829 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (σ y) := by
    first
    | (have i₁ := eq21193 x
       have i₂ := eq33803
       grind)
    | exact superpose eq33803 eq21193
    | exact resolve eq21193 eq33803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33803
  have eq33848 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq33829
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq33829
    | exact resolve eq33829 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33829
  have eq33850 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (σ y) := by
    first
    | (have i₁ := eq33825
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq33825
    | exact resolve eq33825 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33825
  have eq33869 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (σ y) := by
    first
    | (have i₁ := eq33848
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq33848
    | exact resolve eq33848 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33848
  have eq33881 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (σ y) := by
    first
    | exact superpose eq26 eq33869
    | exact resolve eq33869 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33869
  have eq33887 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq33850 eq33881
    | exact resolve eq33881 eq33850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33881
  have eq33895 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq33887 eq27
    | exact resolve eq27 eq33887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33887
  have eq34106 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq33850 eq22219
    | exact resolve eq22219 eq33850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33850
  have eq34141 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq34106
    | exact resolve eq34106 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34106
  have eq34186 : y = (σ y) := by
    first
    | (have r₁ := eq34141
       have r₂ := eq33895
       grind)
    | exact resolve eq34141 eq33895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33895 eq34141
  have eq34211 : (M.op x y) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq34186
       grind)
    | exact superpose eq34186 eq18
    | exact resolve eq18 eq34186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37199 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq19225 x
       have i₂ := eq33756
       grind)
    | exact superpose eq33756 eq19225
    | exact resolve eq19225 eq33756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19225
  have eq37203 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq21193 x
       have i₂ := eq33756
       grind)
    | exact superpose eq33756 eq21193
    | exact resolve eq21193 eq33756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21193 eq33756
  have eq37226 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ y)) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq37203
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37203
    | exact resolve eq37203 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq37203
  have eq37230 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq37199
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq37199
    | exact resolve eq37199 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq37199
  have eq37256 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq37226
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37226
    | exact resolve eq37226 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq37226
  have eq37260 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq37230
       have i₂ := eq34186
       grind)
    | exact superpose eq34186 eq37230
    | exact resolve eq37230 eq34186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37230
  have eq37286 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq37256
    | exact resolve eq37256 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37256
  have eq37308 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq37286
       have i₂ := eq34186
       grind)
    | exact superpose eq34186 eq37286
    | exact resolve eq37286 eq34186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34186 eq37286
  have eq37324 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37260 eq37308
    | exact resolve eq37308 eq37260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37308
  have eq37347 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq37324 eq603
    | exact resolve eq603 eq37324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37428 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37324 eq578
    | exact resolve eq578 eq37324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578 eq37324
  have eq37431 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq37428
    | exact resolve eq37428 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37428
  have eq37621 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq37431
  have eq37961 : (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37347 eq34211
    | exact resolve eq34211 eq37347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34211 eq37347
  have eq37968 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq37961
       have r₂ := eq37621
       grind)
    | exact resolve eq37961 eq37621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37621 eq37961
  have eq38027 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq37968 eq27
    | exact resolve eq27 eq37968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq38028 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (M.op X0 (M.op (σ x) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq37968 eq603
    | exact resolve eq603 eq37968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq38086 : (M.op (σ x) (M.op x y)) = (σ (M.op (σ x) (M.op x y))) := by
    first
    | exact superpose eq37968 eq22219
    | exact resolve eq22219 eq37968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22219
  have eq38678 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq38028 eq556
    | exact resolve eq556 eq38028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556 eq38028
  have eq40786 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq37260 eq38678
    | exact resolve eq38678 eq37260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37260 eq38678
  have eq40789 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq40786
    | exact resolve eq40786 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq40786
  have eq40866 : (M.op x y) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq37968 eq40789
    | exact resolve eq40789 eq37968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40789
  have eq40915 : (M.op x y) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq37968 eq40866
    | exact resolve eq40866 eq37968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37968 eq40866
  have eq40916 : (M.op x y) = (M.op (σ x) (M.op x y)) := by grind
  clear eq40915
  have eq40996 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq40916 eq38086
    | exact resolve eq38086 eq40916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38086 eq40916
  have eq41102 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq40996 eq20
    | exact resolve eq20 eq40996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq40996
  have eq41251 : False := by grind
  exact eq41251

/-- `Equation4428`: `x ◇ (x ◇ y) = (z ◇ w) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_y_pyx_x_pyx_Equation4428 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4428 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4428.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X1) := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
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
  have eq63 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X4 X5) X2) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq9 x X2 X4 X5
       have i₂ := eq9 x X2 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X2 X3) ∨ (k (M.op X2 X3) X1) = (M.op X1 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op X2 X3) X1
       have i₂ := eq9 X0 X1 X2 X3
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X2 X3) X1
       grind)
    | (have r₁ := eq12 (M.op (M.op X2 X3) X1) (M.op (M.op (M.op X2 X3) X1) X1)
       have r₂ := eq9 (M.op (M.op X2 X3) X1) X1 X2 X3
       grind)
    | (have r₁ := eq12 (M.op X0 (M.op X0 X1)) X1
       have r₂ := eq9 X0 X1 X0 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (M.op X0 X2) ∨ (M.op X0 X3) = (k X3 X0) ∨ (M.op X3 X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 X0 X0
       have i₂ := eq14 X3 X0
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X3 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq505 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq479 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq526 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq505 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq505 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq505 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq527 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (M.op X0 X2) ∨ (M.op X0 X3) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq478 X0 X1 X2 X3
       have j1 := eq12 X3 X0
       grind)
    | (have r₁ := eq478 X0 (M.op X0 X2) X2 X3
       have r₂ := eq12 (M.op X0 X2) (M.op (M.op X0 X2) X2)
       grind)
    | (have r₁ := eq478 (M.op X1 (M.op X1 X1)) X1 X1 X3
       have r₂ := eq12 (M.op X1 (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq478 X1 X1 X2 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq478 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq546 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X0
       have i₂ := eq526 X0 X1
       grind)
    | exact superpose eq526 eq14
    | (have j0 := eq14 X1 X0
       have j1 := eq526 X0 X1
       grind)
    | exact resolve eq14 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) X0
       have i₂ := eq526 (σ X0) X1
       grind)
    | exact superpose eq526 eq22
    | (have j1 := eq526 (σ X0) X1
       grind)
    | exact resolve eq22 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq553 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq526 X0 (τ X1)
       grind)
    | exact superpose eq526 eq17
    | (have j1 := eq526 X0 X1
       grind)
    | exact resolve eq17 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq526
  have eq559 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq546 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq567 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq547 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq547
    | (have j0 := eq547 X0 X1
       grind)
    | exact resolve eq547 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq711 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq567 X0 (σ X1)
       grind)
    | exact superpose eq567 eq15
    | (have j1 := eq567 X0 X1
       grind)
    | exact resolve eq15 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq4320 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq553 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq553
    | (have j0 := eq553 X1 X1
       grind)
    | exact resolve eq553 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq4390 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4320 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4320
    | (have j0 := eq4320 X0 X1
       grind)
    | exact resolve eq4320 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4320
  have eq9368 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4390 X1 X0
       have i₂ := eq711 X0 X1
       grind)
    | exact superpose eq711 eq4390
    | (have j0 := eq4390 X0 X0
       have j1 := eq711 X0 X1
       grind)
    | exact resolve eq4390 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq4390
  have eq9413 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq9368 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9368
  have eq11914 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9413 x y
       grind)
    | exact superpose eq9413 eq16
    | (have j1 := eq9413 x x
       grind)
    | (have r₁ := eq16
       have r₂ := eq9413 x y
       grind)
    | exact resolve eq16 eq9413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9413
  have eq12028 : x = (k x x) := by grind
  clear eq11914
  have eq12113 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq559 x x
       have i₂ := eq12028
       grind)
    | exact superpose eq12028 eq559
    | (have j0 := eq559 x x
       grind)
    | exact resolve eq559 eq12028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12117 : x = (M.op x x) := by grind
  clear eq12113
  have eq12125 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x x
       have i₂ := eq12117
       grind)
    | exact superpose eq12117 eq9
    | exact resolve eq9 eq12117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12134 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op x X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X0 X1 X2 x x
       have i₂ := eq12117
       grind)
    | exact superpose eq12117 eq63
    | exact resolve eq63 eq12117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq12117
  have eq14749 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X1)) X1) = (M.op X1 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq138 X0 X1 X0 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq30190 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq469 x x
       have i₂ := eq12028
       grind)
    | exact superpose eq12028 eq469
    | (have j0 := eq469 x x
       grind)
    | exact resolve eq469 eq12028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469 eq12028
  have eq30325 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq30190
  have eq30462 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12134 (σ x) (σ x) X0
       have i₂ := eq30325
       grind)
    | exact superpose eq30325 eq12134
    | exact resolve eq12134 eq30325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30325
  have eq30504 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30462 (σ y)
       grind)
    | exact superpose eq30462 eq16
    | exact resolve eq16 eq30462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30462
  have eq31168 : ∀ X0 X1 : G, (M.op x (σ y)) ≠ (σ (M.op (M.op X0 X1) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq30504
       have i₂ := eq12134 X0 X1 y
       grind)
    | exact superpose eq12134 eq30504
    | exact resolve eq30504 eq12134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30504
  have eq31859 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (σ y)) ≠ (σ (M.op (M.op X2 X3) y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq31168 X2 X3
       have i₂ := eq12134 X0 X1 (σ y)
       grind)
    | exact superpose eq12134 eq31168
    | exact resolve eq31168 eq12134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31168
  have eq33012 : ∀ X0 X1 X3 : G, (k (M.op X0 X1) X1) = (M.op X1 (M.op X0 X1)) ∨ (M.op X0 X3) = (k X3 X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14749 X1 x
       have i₂ := eq527 X0 X1 x X3
       grind)
    | exact superpose eq527 eq14749
    | (have j1 := eq527 X1 X1 x (M.op X0 X1)
       grind)
    | exact resolve eq14749 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527 eq14749
  have eq39778 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op (M.op X0 X1) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq31859 X0 X1 x x
       have i₂ := eq12134 x x y
       grind)
    | exact superpose eq12134 eq31859
    | exact resolve eq31859 eq12134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12134 eq31859
  have eq39905 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq39778 x x
       have i₂ := eq9 X0 (σ y) x x
       grind)
    | exact superpose eq9 eq39778
    | exact resolve eq39778 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39778
  have eq834792 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq33012 X0 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33012
  have eq834793 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq834792 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834792
  have eq834821 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq834793 X0
       have i₂ := eq559 X0 X1
       grind)
    | exact superpose eq559 eq834793
    | (have j1 := eq559 X0 X0
       grind)
    | exact resolve eq834793 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq835196 : ∀ X0 : G, (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq834793 (τ X0)
       grind)
    | exact superpose eq834793 eq18
    | exact resolve eq18 eq834793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq835243 : ∀ X0 : G, (σ (M.op x (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq835196 X0
       have i₂ := eq12125 (τ X0) (τ X0)
       grind)
    | exact superpose eq12125 eq835196
    | exact resolve eq835196 eq12125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12125 eq835196
  have eq835355 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq834821 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834821
  have eq835356 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq835355 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835355
  have eq840106 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq835356 (τ X0)
       grind)
    | exact superpose eq835356 eq31
    | exact resolve eq31 eq835356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq840204 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq840106 X0
       have i₂ := eq835356 X0
       grind)
    | exact superpose eq835356 eq840106
    | exact resolve eq840106 eq835356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835356 eq840106
  have eq840580 : ∀ X0 : G, (σ (M.op x (τ X0))) = (k (σ (τ (M.op X0 X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq835243 X0
       have i₂ := eq840204 X0
       grind)
    | exact superpose eq840204 eq835243
    | exact resolve eq835243 eq840204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835243 eq840204
  have eq840890 : ∀ X0 : G, (σ (M.op x (τ X0))) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq840580 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq840580
    | exact resolve eq840580 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840580
  have eq840915 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ (M.op x (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq840890 X0
       have i₂ := eq834793 X0
       grind)
    | exact superpose eq834793 eq840890
    | exact resolve eq840890 eq834793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834793 eq840890
  have eq863065 : (σ (M.op x y)) ≠ (σ (M.op x (τ (σ y)))) := by
    first
    | (have i₁ := eq39905 (σ y)
       have i₂ := eq840915 (σ y)
       grind)
    | exact superpose eq840915 eq39905
    | exact resolve eq39905 eq840915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39905 eq840915
  have eq863750 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq863065
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq863065
    | exact resolve eq863065 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863065
  have eq863751 : False := by grind
  exact eq863751

/-- `Equation4428`: `x ◇ (x ◇ y) = (z ◇ w) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pyx_x_pyx_Equation4428 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4428 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4428.models_iff G M).mp hM
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X1) := by
    intro X0 X1 X2 X3
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
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
  have eq51 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) (M.op X3 X2)) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 X3 (M.op X3 X2) X4 X5
       have i₂ := eq14 X3 X2 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq78 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq90 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq78
       grind)
    | exact superpose eq78 eq16
    | exact resolve eq16 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq77
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq77
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq77 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq102
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq103
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq103
    | exact resolve eq103 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq114
    | exact resolve eq114 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq159 : (σ (k (k x x) x)) = (k (k (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq40 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq40
    | exact resolve eq40 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq193 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq213 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq57 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq57
    | (have j0 := eq57 x y
       grind)
    | exact resolve eq57 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 x X2
       have i₂ := eq14 x X2 X0 X1
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X1 : G, (M.op (M.op x y) X1) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X1
    first
    | (have i₁ := eq58 x X1
       have i₂ := eq57 x X1
       grind)
    | exact superpose eq57 eq58
    | exact resolve eq58 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq232 : (k (M.op (M.op x y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (σ x) (σ y)))) := by grind
  have eq233 : (k (M.op (M.op x y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq226 eq232
    | exact resolve eq232 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq232
  have eq237 : (M.op (M.op x y) (M.op (σ x) (σ y))) = (k (M.op (M.op x y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq233
       have i₂ := eq57 sF0 sF4
       grind)
    | exact superpose eq57 eq233
    | exact resolve eq233 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq276 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 X0
       have i₂ := eq11 (τ X1) X0
       grind)
    | exact superpose eq11 eq35
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq35 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  clear eq39
  have eq367 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op x y) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq346 X0
       have i₂ := eq57 (τ X0) (τ X0)
       grind)
    | exact superpose eq57 eq346
    | exact resolve eq346 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq447 : ∀ X2 X3 X4 X5 : G, (M.op (M.op X4 X5) (M.op X3 X2)) = (M.op X3 (M.op (M.op x y) X2)) := by
    intro X2 X3 X4 X5
    first
    | (have i₁ := eq51 x x X2 X3 X4 X5
       have i₂ := eq215 x x X2
       grind)
    | (have i₁ := eq51 x y X2 X3 X4 X5
       have i₂ := eq215 x x X2
       grind)
    | exact superpose eq215 eq51
    | (have j0 := eq51 x y X2 X3 X4 X5
       grind)
    | exact resolve eq51 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq448 : ∀ X2 X3 : G, (M.op (M.op x y) (M.op X3 X2)) = (M.op X3 (M.op (M.op x y) X2)) := by
    intro X2 X3
    first
    | (have i₁ := eq447 X2 X3 x x
       have i₂ := eq215 x x (M.op X3 X2)
       grind)
    | (have i₁ := eq447 X2 X3 x y
       have i₂ := eq215 x x (M.op X3 X2)
       grind)
    | exact superpose eq215 eq447
    | (have j0 := eq447 X2 X3 x y
       grind)
    | exact resolve eq447 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq536 : ∀ X0 : G, (k (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X0)) (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) X0) (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X0))) := by
    intro X0
    grind
  have eq546 : ∀ X0 : G, (k (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X0)) (M.op (M.op x y) X0)) = (M.op (M.op x y) (M.op (M.op (M.op x y) X0) (M.op (M.op (M.op x y) X0) X0))) := by
    intro X0
    first
    | exact superpose eq448 eq536
    | exact resolve eq536 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448 eq536
  have eq560 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = (k (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X0)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq546 x
       have i₂ := eq57 (M.op sF0 x) x
       grind)
    | exact superpose eq57 eq546
    | exact resolve eq546 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq567 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = (k (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq560 x
       have i₂ := eq215 sF0 x x
       grind)
    | exact superpose eq215 eq560
    | exact resolve eq560 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq570 : ∀ X0 : G, (M.op (M.op x y) X0) = (k (M.op (M.op x y) X0) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq567 x
       have i₂ := eq57 sF0 x
       grind)
    | exact superpose eq57 eq567
    | exact resolve eq567 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq898 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq900 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq96 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq901 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq900 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq903 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq898 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq905 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq903 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq903
    | (have j0 := eq903 X0
       grind)
    | exact resolve eq903 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq3788 : ∀ X0 : G, (σ (M.op (M.op x y) X0)) ≠ (σ (M.op (M.op x y) X0)) ∨ (σ (M.op (M.op x y) X0)) = (M.op (σ (M.op (M.op x y) X0)) (σ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq570 eq901
    | (have j0 := eq901 (M.op (M.op x y) X0)
       grind)
    | exact resolve eq901 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3793 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq901 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq901
    | (have j0 := eq901 (τ X0)
       grind)
    | exact resolve eq901 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq901
  have eq3798 : ∀ X0 : G, (σ (M.op (M.op x y) X0)) = (M.op (σ (M.op (M.op x y) X0)) (σ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | (have j0 := eq3788 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3788
  have eq3803 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3793 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3793
    | (have j0 := eq3793 X0
       grind)
    | exact resolve eq3793 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3793
  have eq3809 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3803 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3803
    | (have j0 := eq3803 X0
       grind)
    | exact resolve eq3803 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3803
  have eq4128 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq193 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq193
    | (have j0 := eq193 y
       grind)
    | exact resolve eq193 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq4138 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq4128
  have eq4144 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4138
       have i₂ := eq78
       grind)
    | exact superpose eq78 eq4138
    | exact resolve eq4138 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq4138
  have eq4902 : ∀ X0 : G, (σ (M.op (M.op x y) (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq367 X0
       have i₂ := eq276 (τ X0) X0
       grind)
    | exact superpose eq276 eq367
    | (have j1 := eq276 (τ X0) X0
       grind)
    | exact resolve eq367 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276 eq367
  have eq4927 : ∀ X0 : G, (σ (M.op (M.op x y) (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq4902 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4902
  have eq4931 : ∀ X0 : G, (σ (M.op (M.op x y) (τ X0))) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq4927 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4927
    | (have j0 := eq4927 X0
       grind)
    | exact resolve eq4927 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4927
  have eq5119 : (σ (k (k x x) x)) = (M.op (σ x) (σ (k x x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq905 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq905
    | (have j0 := eq905 x
       grind)
    | exact resolve eq905 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq5167 : (σ (k (k x x) x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5119
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq5119
    | exact resolve eq5119 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq5119
  have eq5184 : (k (k (σ x) (σ x)) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5167
       have i₂ := eq159
       grind)
    | exact superpose eq159 eq5167
    | exact resolve eq5167 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq5167
  have eq18324 : ∀ X0 : G, (M.op (σ (M.op (M.op x y) X0)) (σ (M.op (M.op x y) X0))) = (M.op (M.op x y) (σ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq3798 eq57
    | exact resolve eq57 eq3798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18325 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (σ (M.op (M.op x y) X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq3798 eq215
    | exact resolve eq215 eq3798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18336 : ∀ X0 : G, (σ (M.op (M.op x y) X0)) = (M.op (M.op x y) (σ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq3798 eq18324
    | exact resolve eq18324 eq3798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3798 eq18324
  have eq18558 : (σ (M.op x (M.op x y))) = (M.op (M.op x y) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq213 eq18336
    | exact resolve eq18336 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18336
  have eq19712 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19713 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq19712
    | exact resolve eq19712 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19712
  have eq19724 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq19713
       have r₂ := eq28
       grind)
    | exact resolve eq19713 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19713
  have eq19728 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq19724
  have eq19743 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq19728
    | exact resolve eq19728 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19728
  have eq19782 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq19743 eq115
    | exact resolve eq115 eq19743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq19743
  have eq19795 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq19782
  have eq19798 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq19795
       have r₂ := eq28
       grind)
    | exact resolve eq19795 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19795
  have eq19804 : (M.op (σ x) (σ x)) = (M.op (M.op x y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq19798 eq57
    | exact resolve eq57 eq19798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20128 : (σ x) = (M.op (M.op x y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq19804 eq19798
    | exact resolve eq19798 eq19804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19798 eq19804
  have eq20142 : (σ x) = (M.op (M.op x y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq20128
  have eq20451 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20142 eq570
    | exact resolve eq570 eq20142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570 eq20142
  have eq20573 : (τ (σ x)) = (k x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20451 eq50
    | exact resolve eq50 eq20451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq20451
  have eq20612 : x = (k x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq20573
    | exact resolve eq20573 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq20573
  have eq20615 : y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq3809 x
       grind)
    | (have r₁ := eq20612
       have r₂ := eq3809 x
       grind)
    | exact resolve eq20612 eq3809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3809 eq20612
  have eq20616 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq113
       have i₂ := eq20615
       grind)
    | exact superpose eq20615 eq113
    | exact resolve eq113 eq20615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq20618 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by grind
  have eq20628 : x ≠ y ∨ x = (M.op x x) := by grind
  clear eq20615
  have eq20635 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq20618
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20618
    | exact resolve eq20618 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20618
  have eq20636 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq20616
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20616
    | exact resolve eq20616 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20616
  have eq20679 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq77
       have i₂ := eq20635
       grind)
    | exact superpose eq20635 eq77
    | exact resolve eq77 eq20635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq20635
  have eq20708 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq20679
    | exact resolve eq20679 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20679
  have eq23901 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq20636
       have r₂ := eq20628
       grind)
    | exact resolve eq20636 eq20628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20628 eq20636
  have eq23928 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq23901 eq5184
    | exact resolve eq5184 eq23901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5184
  have eq23952 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq23928
    | exact resolve eq23928 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23928
  have eq62618 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq23952 eq20708
    | exact resolve eq20708 eq23952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23952
  have eq62639 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq62618
  have eq62652 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq62639
       have r₂ := eq28
       grind)
    | exact resolve eq62639 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62639
  have eq62660 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq62652
  have eq62701 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq62660 eq23901
    | exact resolve eq23901 eq62660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23901 eq62660
  have eq62726 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq62701
  have eq62744 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq62726
  have eq62770 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq62744
    | exact resolve eq62744 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62744
  have eq62874 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq62770 eq20708
    | exact resolve eq20708 eq62770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20708 eq62770
  have eq62894 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq62874
  have eq62906 : x = (M.op x x) := by
    first
    | (have r₁ := eq62894
       have r₂ := eq28
       grind)
    | exact resolve eq62894 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62894
  have eq62912 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq57 x x
       have i₂ := eq62906
       grind)
    | exact superpose eq62906 eq57
    | exact resolve eq57 eq62906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62913 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq215 x x X0
       have i₂ := eq62906
       grind)
    | exact superpose eq62906 eq215
    | exact resolve eq215 eq62906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq62925 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq62912
       have i₂ := eq62906
       grind)
    | exact superpose eq62906 eq62912
    | exact resolve eq62912 eq62906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62906 eq62912
  have eq62977 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq62925 eq18325
    | exact resolve eq18325 eq62925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18325 eq62925
  have eq63006 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq62977 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq62977
    | (have j0 := eq62977 X0
       grind)
    | exact resolve eq62977 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq62977
  have eq63393 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq62913 eq213
    | exact resolve eq213 eq62913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63508 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq63393
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq63393
    | exact resolve eq63393 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63393
  have eq63616 : (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq63508 eq18558
    | exact resolve eq18558 eq63508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18558
  have eq63648 : (σ (M.op x y)) = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq62913 eq63616
    | exact resolve eq63616 eq62913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63616
  have eq63665 : (σ (M.op x y)) = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq63648
    | exact resolve eq63648 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63648
  have eq64316 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq62913 eq63006
    | exact resolve eq63006 eq62913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63006
  have eq64330 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq27 eq64316
    | (have j0 := eq64316 (σ y)
       grind)
    | exact resolve eq64316 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq64316
  have eq135350 : ∀ X0 : G, (k (k X0 X0) X0) = (σ (M.op x (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | exact superpose eq62913 eq4931
    | (have j0 := eq4931 X0
       grind)
    | exact resolve eq4931 eq62913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4931
  have eq135933 : (k (M.op (σ y) (σ y)) (σ y)) = (σ (M.op x (τ (σ y)))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq4144 eq135350
    | (have j0 := eq135350 (σ y)
       grind)
    | exact resolve eq135350 eq4144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4144 eq135350
  have eq136293 : (σ (M.op x y)) = (k (M.op (σ y) (σ y)) (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq30 eq135933
    | exact resolve eq135933 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135933
  have eq136464 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq136293
  have eq136542 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq136464
       have i₂ := eq57 sF3 sF3
       grind)
    | exact superpose eq57 eq136464
    | exact resolve eq136464 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136464
  have eq136596 : (σ (M.op x y)) = (M.op x (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq62913 eq136542
    | exact resolve eq136542 eq62913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136542
  have eq136633 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq64330 eq136596
    | exact resolve eq136596 eq64330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136596
  have eq136664 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq136633
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq136633
    | exact resolve eq136633 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq136633
  have eq136676 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq21 eq136664
    | exact resolve eq136664 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136664
  have eq136687 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq136676
       have r₂ := eq28
       grind)
    | exact resolve eq136676 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136676
  have eq136697 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq136687
    | exact resolve eq136687 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136687
  have eq136720 : (M.op (σ y) (σ y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq136697 eq57
    | exact resolve eq57 eq136697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136744 : (M.op (σ y) (σ y)) = (M.op x (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq62913 eq136720
    | exact resolve eq136720 eq62913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136720
  have eq136754 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq64330 eq136744
    | exact resolve eq136744 eq64330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136744
  have eq136782 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq136754 eq136697
    | exact resolve eq136697 eq136754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136697 eq136754
  have eq136799 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq136782
  have eq137382 : (M.op y y) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq57 y y
       have i₂ := eq136799
       grind)
    | exact superpose eq136799 eq57
    | exact resolve eq57 eq136799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137410 : (M.op y y) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq213 eq137382
    | exact resolve eq137382 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137382
  have eq137427 : (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq63508 eq137410
    | exact resolve eq137410 eq63508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137410
  have eq137998 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq136799
       have i₂ := eq137427
       grind)
    | exact superpose eq137427 eq136799
    | exact resolve eq136799 eq137427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136799 eq137427
  have eq138022 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq137998
  have eq138552 : (M.op (M.op x y) (σ y)) = (k (M.op (M.op x y) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq138022 eq237
    | exact resolve eq237 eq138022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq138581 : (M.op x (σ y)) = (k (M.op x (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq62913 eq138552
    | exact resolve eq138552 eq62913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62913 eq138552
  have eq138586 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq64330 eq138581
    | exact resolve eq138581 eq64330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138581
  have eq140097 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq138022 eq138586
    | exact resolve eq138586 eq138022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138022 eq138586
  have eq140105 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq140097
  have eq140121 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq140105 eq90
    | exact resolve eq90 eq140105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq140105
  have eq140169 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq140121
    | exact resolve eq140121 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq140121
  have eq140255 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq140169
       grind)
    | exact superpose eq140169 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq140169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140169
  have eq140256 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq140255
  have eq140370 : (M.op y y) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq57 y y
       have i₂ := eq140256
       grind)
    | exact superpose eq140256 eq57
    | exact resolve eq57 eq140256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq140400 : (M.op y y) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq213 eq140370
    | exact resolve eq140370 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq140370
  have eq140417 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq63508 eq140400
    | exact resolve eq140400 eq63508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63508 eq140400
  have eq140824 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq140256
       have i₂ := eq140417
       grind)
    | exact superpose eq140417 eq140256
    | exact resolve eq140256 eq140417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140256 eq140417
  have eq140851 : y = (M.op x y) := by grind
  clear eq140824
  have eq140899 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq140851 eq21
    | exact resolve eq21 eq140851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq140851
  have eq141410 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq140899
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq140899
    | exact resolve eq140899 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq140899
  have eq141582 : (M.op (σ x) (σ y)) = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq141410 eq64330
    | exact resolve eq64330 eq141410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64330 eq141410
  have eq141599 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq63665 eq141582
    | exact resolve eq141582 eq63665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63665 eq141582
  have eq141675 : False := by grind
  exact eq141675

/-- `Equation4428`: `x ◇ (x ◇ y) = (z ◇ w) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_x_pxy_pyx_Equation4428 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4428 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4428.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X1) := by
    intro X0 X1 X2 X3
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
  clear eq43
  have eq59 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) (M.op X3 X2)) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 X3 (M.op X3 X2) X4 X5
       have i₂ := eq14 X3 X2 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) ≠ (M.op X0 (M.op X0 (M.op X1 X2))) ∨ (k X3 (M.op X1 X2)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 (M.op X1 X2)
       have i₂ := eq14 X0 (M.op X1 X2) X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X3 (M.op X1 X2)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq77 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq79 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X1 (M.op X2 X3)) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 (M.op X0 X1)) = (k (M.op X2 X3) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op X2 X3) X1
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | (have r₁ := eq12 X3 (M.op X3 X3)
       have r₂ := eq14 X3 X3 X3 X3
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq14 X0 X0 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : (σ (k (k y y) y)) = (k (k (σ y) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq40 (k y y)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq40
    | exact resolve eq40 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq206 : (M.op x (M.op x y)) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq65 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq65
    | (have j0 := eq65 x y
       grind)
    | exact resolve eq65 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 x X2
       have i₂ := eq14 x X2 X0 X1
       grind)
    | exact superpose eq14 eq65
    | exact resolve eq65 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq279 : ∀ X0 X1 : G, (σ (k (k (τ X0) X1) y)) = (k (k X0 (σ X1)) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq40 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq40
    | exact resolve eq40 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq113 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq113
    | (have j0 := eq113 (σ X0)
       grind)
    | exact resolve eq113 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq473 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq274 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq274
    | exact resolve eq274 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq514 : ∀ X2 X3 X4 X5 : G, (M.op (M.op X4 X5) (M.op X3 X2)) = (M.op X3 (M.op (M.op x y) X2)) := by
    intro X2 X3 X4 X5
    first
    | (have i₁ := eq59 x x X2 X3 X4 X5
       have i₂ := eq208 x x X2
       grind)
    | (have i₁ := eq59 x y X2 X3 X4 X5
       have i₂ := eq208 x x X2
       grind)
    | exact superpose eq208 eq59
    | (have j0 := eq59 x y X2 X3 X4 X5
       grind)
    | exact resolve eq59 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq515 : ∀ X2 X3 : G, (M.op (M.op x y) (M.op X3 X2)) = (M.op X3 (M.op (M.op x y) X2)) := by
    intro X2 X3
    first
    | (have i₁ := eq514 X2 X3 x x
       have i₂ := eq208 x x (M.op X3 X2)
       grind)
    | (have i₁ := eq514 X2 X3 x y
       have i₂ := eq208 x x (M.op X3 X2)
       grind)
    | exact superpose eq208 eq514
    | (have j0 := eq514 X2 X3 x y
       grind)
    | exact resolve eq514 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq591 : ∀ X0 X1 : G, (M.op (M.op x y) X0) ≠ (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X0)) ∨ (k X1 (M.op (M.op x y) X0)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq515 eq13
    | (have j0 := eq13 X1 (M.op (M.op x y) X0)
       grind)
    | exact resolve eq13 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : ∀ X0 X1 : G, (M.op (M.op x y) X0) ≠ (M.op (M.op x y) (M.op (M.op x y) X0)) ∨ (k X1 (M.op (M.op x y) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq591 x X1
       have i₂ := eq208 sF0 x x
       grind)
    | exact superpose eq208 eq591
    | (have j0 := eq591 X0 X1
       grind)
    | exact resolve eq591 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq625 : ∀ X0 X1 : G, (k X1 (M.op (M.op x y) X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq611 X0 X1
       grind)
    | (have r₁ := eq611 X1 X1
       have r₂ := eq65 (M.op x y) X1
       grind)
    | exact resolve eq611 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq632 : ∀ X0 : G, (k X0 (M.op x (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq206 eq625
    | exact resolve eq625 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq814 : ∀ X1 X2 X3 : G, (M.op X1 X2) ≠ (M.op (M.op x y) (M.op X1 X2)) ∨ (k X3 (M.op X1 X2)) = X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq69 x X1 X2 X3
       have i₂ := eq65 x (M.op X1 X2)
       grind)
    | exact superpose eq65 eq69
    | (have j0 := eq69 x X1 X2 X3
       grind)
    | exact resolve eq69 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq854 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 (M.op (M.op x y) X1)) ∨ (k X2 (M.op X0 X1)) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq515 eq814
    | (have j0 := eq814 X0 X1 X2
       grind)
    | exact resolve eq814 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515 eq814
  have eq960 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x y) X1) ≠ (M.op X1 (M.op X2 X3)) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 (M.op X0 X1)) = (k (M.op X2 X3) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq111 X0 X1 X2 X3
       have i₂ := eq65 X0 X1
       grind)
    | exact superpose eq65 eq111
    | (have j0 := eq111 X0 X1 X2 X3
       grind)
    | (have r₁ := eq111 X0 (M.op x y) x y
       have r₂ := eq65 X0 (M.op x y)
       grind)
    | (have r₁ := eq111 (M.op x y) X0 X0 (M.op (M.op x y) X0)
       have r₂ := eq65 X0 (M.op (M.op x y) X0)
       grind)
    | exact resolve eq111 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq961 : ∀ X1 X2 X3 : G, (M.op (M.op x y) X1) ≠ (M.op X1 (M.op X2 X3)) ∨ (M.op (M.op x y) X1) = (k (M.op X2 X3) X1) ∨ (M.op X1 X1) = X1 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq960 x X1 X2 X3
       have i₂ := eq65 x X1
       grind)
    | exact superpose eq65 eq960
    | (have j0 := eq960 x X1 X2 X3
       grind)
    | (have r₁ := eq960 x x x x
       have r₂ := eq65 x x
       grind)
    | exact resolve eq960 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq1007 : ∀ X0 X1 : G, (M.op (M.op x y) X1) ≠ (M.op (M.op x y) X0) ∨ (M.op (M.op x y) X1) = (k (M.op X1 X0) X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq961 X1 X1 X0
       have i₂ := eq65 X1 X0
       grind)
    | exact superpose eq65 eq961
    | (have j0 := eq961 X1 X1 X0
       grind)
    | (have r₁ := eq961 X0 X0 X0
       have r₂ := eq65 X0 X0
       grind)
    | exact resolve eq961 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1131 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq79 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq12
    | (have j0 := eq12 X0 (σ X0)
       have j1 := eq79 X1 X0
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq79 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq12 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq1141 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1131 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131
  have eq1142 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1141 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq1148 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1142 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq1142
    | (have j0 := eq1142 X0 X1
       grind)
    | exact resolve eq1142 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142
  have eq1149 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1148 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148
  have eq2698 : ∀ X0 : G, (k (k X0 (σ (τ X0))) (σ y)) = (σ (k (M.op (τ X0) (τ X0)) y)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq279 X0 (τ X0)
       have i₂ := eq113 (τ X0)
       grind)
    | exact superpose eq113 eq279
    | (have j1 := eq113 (τ X0)
       grind)
    | exact resolve eq279 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq2782 : ∀ X0 : G, (σ (k (M.op (τ X0) (τ X0)) y)) = (k (k X0 X0) (σ y)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2698 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2698
    | (have j0 := eq2698 X0
       grind)
    | exact resolve eq2698 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2698
  have eq5526 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq457 X0
       grind)
    | exact superpose eq457 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq457 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq457 X0
       grind)
    | exact resolve eq13 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5536 : ∀ X0 X1 : G, (M.op (M.op x y) X1) ≠ (M.op X1 (σ (k X0 X0))) ∨ (M.op (M.op x y) X1) = (k (σ (k X0 X0)) X1) ∨ (M.op X1 X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq961 X1 (σ X0) (σ X0)
       have i₂ := eq457 X0
       grind)
    | exact superpose eq457 eq961
    | (have j0 := eq961 X1 x x
       have j1 := eq457 X0
       grind)
    | exact resolve eq961 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961
  have eq5538 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq457 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq5545 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5526 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq5526 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq5526 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5526
  have eq5846 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1149 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1149
    | exact resolve eq1149 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5927 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1149 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1149
    | (have j0 := eq1149 x X0
       grind)
    | exact resolve eq1149 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6023 : ∀ X0 X1 : G, (M.op (M.op x y) (σ X0)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq65 (σ X1) (σ X0)
       have i₂ := eq1149 X1 X0
       grind)
    | exact superpose eq1149 eq65
    | (have j1 := eq1149 X1 X1
       grind)
    | exact resolve eq65 eq1149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149
  have eq6047 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5846 X0 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq5846
    | (have j0 := eq5846 X0 X1
       grind)
    | exact resolve eq5846 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq5846
  have eq6073 : ∀ X0 : G, (M.op x (M.op x y)) ≠ (M.op (M.op x y) X0) ∨ (M.op x (M.op x y)) = (k (M.op y X0) y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq206 eq1007
    | (have j0 := eq1007 X0 y
       grind)
    | exact resolve eq1007 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq16671 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5545 (τ X0) X1
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq5545
    | (have j0 := eq5545 (τ X0) X1
       grind)
    | exact resolve eq5545 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq16722 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16671 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq16671
    | (have j0 := eq16671 X0 X1
       grind)
    | exact resolve eq16671 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16671
  have eq16747 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16722 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq16722
    | (have j0 := eq16722 X0 X1
       grind)
    | exact resolve eq16722 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16722
  have eq16780 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16747 (τ X0) X1
       have i₂ := eq473 X0 X0
       grind)
    | exact superpose eq473 eq16747
    | (have j0 := eq16747 (τ X0) X1
       grind)
    | exact resolve eq16747 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq22894 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5927 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5927
    | (have j0 := eq5927 y
       grind)
    | exact resolve eq5927 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5927
  have eq22914 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq22894
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq22894
    | exact resolve eq22894 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22894
  have eq22932 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq22914
    | exact resolve eq22914 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22914
  have eq23465 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6047 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6047
    | (have j0 := eq6047 X1 X1
       grind)
    | exact resolve eq6047 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6047
  have eq24234 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq76
       have i₂ := eq23465 y x
       grind)
    | exact superpose eq23465 eq76
    | (have j1 := eq23465 x x
       grind)
    | exact resolve eq76 eq23465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq23465
  have eq24512 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq24234
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24234
    | exact resolve eq24234 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24234
  have eq24554 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq24512
    | exact resolve eq24512 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24512
  have eq24598 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq24554 eq22932
    | exact resolve eq22932 eq24554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22932 eq24554
  have eq24605 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq24598
       have r₂ := eq27
       grind)
    | exact resolve eq24598 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24598
  have eq24816 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq24605 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq24605
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq24605
       grind)
    | exact resolve eq13 eq24605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24605
  have eq24829 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq24816 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24816
  have eq25114 : ∀ X0 X1 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq24829 X1
       grind)
    | exact superpose eq24829 eq13
    | (have j0 := eq13 X0 x
       have j1 := eq24829 X1
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq24829 X0
       grind)
    | exact resolve eq13 eq24829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24829
  have eq25128 : ∀ X0 X1 : G, (k X1 (σ x)) = X1 ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq25114 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25114
  have eq25165 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq49
       have i₂ := eq25128 (k sF2 sF2) x
       grind)
    | exact superpose eq25128 eq49
    | (have j1 := eq25128 X0 x
       grind)
    | exact resolve eq49 eq25128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq25128
  have eq25252 : ∀ X0 : G, x = (k x x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq25165
    | (have j0 := eq25165 x
       grind)
    | exact resolve eq25165 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq25165
  have eq25288 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq25252 X0
       have j1 := eq16747 x X0
       grind)
    | (have r₁ := eq25252 X0
       have r₂ := eq16747 x x
       grind)
    | (have r₁ := eq25252 x
       have r₂ := eq16747 x x
       grind)
    | exact resolve eq25252 eq16747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16747 eq25252
  have eq25345 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq5545 x X0
       have i₂ := eq25288 x
       grind)
    | exact superpose eq25288 eq5545
    | (have j0 := eq5545 x X0
       grind)
    | exact resolve eq5545 eq25288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5545
  have eq25346 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq113 x
       have i₂ := eq25288 x
       grind)
    | exact superpose eq25288 eq113
    | (have j0 := eq113 x
       grind)
    | exact resolve eq113 eq25288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25369 : x = (M.op x x) := by grind
  clear eq25346
  have eq25370 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq25345 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25345
  have eq25390 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq25370 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25370
    | (have j0 := eq25370 X0
       grind)
    | exact resolve eq25370 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq25370
  have eq25907 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq208 x x X0
       have i₂ := eq25369
       grind)
    | exact superpose eq25369 eq208
    | exact resolve eq208 eq25369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25369
  have eq25982 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq25390 eq113
    | (have j0 := eq113 (σ x)
       grind)
    | exact resolve eq113 eq25390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26006 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq25982
  have eq26162 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq26006 eq208
    | exact resolve eq208 eq26006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26006
  have eq28246 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq25907 eq206
    | exact resolve eq206 eq25907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28352 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq28246
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28246
    | exact resolve eq28246 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28246
  have eq29066 : (σ (M.op x (M.op x y))) ≠ (σ (M.op x (M.op x y))) ∨ (σ (M.op x (M.op x y))) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq632 eq5538
    | (have j0 := eq5538 (M.op x (M.op x y))
       grind)
    | exact resolve eq5538 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632 eq5538
  have eq29199 : (σ (M.op x (M.op x y))) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by grind
  clear eq29066
  have eq29264 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq28352 eq29199
    | exact resolve eq29199 eq28352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29199
  have eq29304 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq29264
    | exact resolve eq29264 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29264
  have eq29328 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq29304 eq65
    | exact resolve eq65 eq29304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29329 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq29304 eq208
    | exact resolve eq208 eq29304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq29348 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq25907 eq29329
    | exact resolve eq29329 eq25907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29329
  have eq29349 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq25907 eq29328
    | exact resolve eq29328 eq25907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29328
  have eq29359 : (σ (M.op x y)) = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq29304 eq29349
    | exact resolve eq29349 eq29304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29304 eq29349
  have eq29836 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) X0) ≠ (M.op x (M.op (M.op x y) X0)) ∨ (k X1 (M.op (σ (M.op x y)) X0)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq29348 eq854
    | (have j0 := eq854 (σ (M.op x y)) X0 X1
       grind)
    | exact resolve eq854 eq29348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq29906 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) X0) ≠ (M.op x (M.op x X0)) ∨ (k X1 (M.op (σ (M.op x y)) X0)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq25907 eq29836
    | (have j0 := eq29836 X0 X1
       grind)
    | exact resolve eq29836 eq25907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29836
  have eq29931 : ∀ X0 X1 : G, (M.op (M.op x y) X0) ≠ (M.op (σ (M.op x y)) X0) ∨ (k X1 (M.op (σ (M.op x y)) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29906 X0 X1
       have i₂ := eq65 x X0
       grind)
    | exact superpose eq65 eq29906
    | (have j0 := eq29906 X0 X1
       grind)
    | exact resolve eq29906 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29906
  have eq29953 : ∀ X0 X1 : G, (M.op (M.op x y) X0) ≠ (M.op x X0) ∨ (k X1 (M.op (σ (M.op x y)) X0)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq29348 eq29931
    | (have j0 := eq29931 X0 X1
       grind)
    | exact resolve eq29931 eq29348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29931
  have eq29973 : ∀ X0 X1 : G, (k X1 (M.op (σ (M.op x y)) X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq29953 X0 X1
       grind)
    | (have r₁ := eq29953 X0 X1
       have r₂ := eq25907 X0
       grind)
    | exact resolve eq29953 eq25907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29953
  have eq29992 : ∀ X0 X1 : G, (k X1 (M.op x X0)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq29348 eq29973
    | exact resolve eq29973 eq29348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29348 eq29973
  have eq30800 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq25907 eq26162
    | exact resolve eq26162 eq25907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26162
  have eq31660 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq26 eq30800
    | (have j0 := eq30800 (σ y)
       grind)
    | exact resolve eq30800 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq30800
  have eq31889 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq31660 eq29992
    | exact resolve eq29992 eq31660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29992
  have eq31942 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) ≠ (τ (M.op (σ x) (σ y))) ∨ (k X0 (τ (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq31889 eq16780
    | (have j0 := eq16780 (M.op (σ x) (σ y)) X0
       grind)
    | exact resolve eq16780 eq31889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16780 eq31889
  have eq31973 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have j0 := eq31942 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31942
  have eq32765 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq31973 eq113
    | (have j0 := eq113 (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq113 eq31973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq31973
  have eq32790 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by grind
  clear eq32765
  have eq57537 : (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq32790 eq65
    | exact resolve eq65 eq32790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57558 : (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (M.op x (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq25907 eq57537
    | exact resolve eq57537 eq25907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57537
  have eq57569 : (τ (M.op (σ x) (σ y))) = (M.op x (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq32790 eq57558
    | exact resolve eq57558 eq32790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32790 eq57558
  have eq169101 : ∀ X0 X1 : G, (M.op (σ X1) (σ (k X0 X1))) = (M.op x (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | exact superpose eq25907 eq6023
    | (have j0 := eq6023 X0 X1
       grind)
    | exact resolve eq6023 eq25907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6023
  have eq170176 : ∀ X0 : G, (M.op (σ y) (σ (k X0 y))) = (M.op x (σ X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq169101 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq169101
    | (have j0 := eq169101 X0 y
       grind)
    | exact resolve eq169101 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169101
  have eq182350 : ∀ X0 : G, (M.op x (M.op x y)) ≠ (M.op x X0) ∨ (M.op x (M.op x y)) = (k (M.op y X0) y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq25907 eq6073
    | (have j0 := eq6073 X0
       grind)
    | (have r₁ := eq6073 (M.op x y)
       have r₂ := eq25907 (M.op x y)
       grind)
    | exact resolve eq6073 eq25907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6073
  have eq182351 : ∀ X0 : G, (M.op x y) ≠ (M.op x X0) ∨ (M.op x (M.op x y)) = (k (M.op y X0) y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq28352 eq182350
    | (have j0 := eq182350 X0
       grind)
    | (have r₁ := eq182350 y
       have r₂ := eq28352
       grind)
    | exact resolve eq182350 eq28352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182350
  have eq182352 : ∀ X0 : G, (M.op x y) ≠ (M.op x X0) ∨ (M.op x y) = (k (M.op y X0) y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq28352 eq182351
    | (have j0 := eq182351 X0
       grind)
    | (have r₁ := eq182351 (M.op x y)
       have r₂ := eq28352
       grind)
    | exact resolve eq182351 eq28352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182351
  have eq182378 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op y y) y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq182352 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq182352
    | (have j0 := eq182352 y
       grind)
    | (have r₁ := eq182352 y
       have r₂ := eq18
       grind)
    | exact resolve eq182352 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182352
  have eq182397 : (M.op x y) = (k (M.op y y) y) ∨ y = (M.op y y) := by grind
  clear eq182378
  have eq193248 : (k (k (k (σ y) (σ x)) (k (σ y) (σ x))) (σ y)) = (σ (k (M.op (k y x) (k y x)) y)) ∨ (k y x) = (M.op (k y x) (k y x)) := by
    first
    | exact superpose eq96 eq2782
    | exact resolve eq2782 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq2782
  have eq193404 : (σ (k (M.op y y) y)) = (k (k (k (σ y) (σ x)) (k (σ y) (σ x))) (σ y)) ∨ (k y x) = (M.op (k y x) (k y x)) := by
    first
    | (have i₁ := eq193248
       have i₂ := eq25288 y
       grind)
    | exact superpose eq25288 eq193248
    | exact resolve eq193248 eq25288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193248
  have eq193480 : (k (k (σ y) (σ y)) (σ y)) = (σ (k (M.op y y) y)) ∨ (k y x) = (M.op (k y x) (k y x)) := by
    first
    | exact superpose eq25390 eq193404
    | exact resolve eq193404 eq25390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25390 eq193404
  have eq193541 : (k (k (σ y) (σ y)) (σ y)) = (σ (k (M.op y y) y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq193480
       have i₂ := eq25288 y
       grind)
    | exact superpose eq25288 eq193480
    | exact resolve eq193480 eq25288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25288 eq193480
  have eq500794 : ∀ X0 X1 : G, (M.op X1 (σ (k X0 X0))) ≠ (M.op x X1) ∨ (M.op (M.op x y) X1) = (k (σ (k X0 X0)) X1) ∨ (M.op X1 X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | exact superpose eq25907 eq5536
    | (have j0 := eq5536 X0 X1
       grind)
    | exact resolve eq5536 eq25907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5536
  have eq500795 : ∀ X0 X1 : G, (M.op X1 (σ (k X0 X0))) ≠ (M.op x X1) ∨ (k (σ (k X0 X0)) X1) = (M.op x X1) ∨ (M.op X1 X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | exact superpose eq25907 eq500794
    | (have j0 := eq500794 X0 X1
       grind)
    | exact resolve eq500794 eq25907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500794
  have eq1513018 : (M.op x (σ y)) ≠ (M.op x (σ y)) ∨ (k (σ (k y y)) (σ y)) = (M.op x (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq170176 eq500795
    | (have j0 := eq500795 y (σ y)
       grind)
    | (have r₁ := eq500795 y (σ y)
       have r₂ := eq170176 y
       grind)
    | exact resolve eq500795 eq170176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170176 eq500795
  have eq1513075 : (M.op x (σ y)) ≠ (M.op x (σ y)) ∨ (k (σ (k y y)) (σ y)) = (M.op x (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1513018
  have eq1513109 : (M.op x (σ y)) ≠ (M.op x (σ y)) ∨ (k (σ (k y y)) (σ y)) = (M.op x (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1513075
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1513075
    | exact resolve eq1513075 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513075
  have eq1513110 : (k (σ (k y y)) (σ y)) = (M.op x (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1513109
  have eq1513188 : (M.op (σ x) (σ y)) = (k (σ (k y y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq31660 eq1513110
    | exact resolve eq1513110 eq31660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513110
  have eq1513231 : (M.op (σ x) (σ y)) = (σ (k (k y y) y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq40 eq1513188
    | exact resolve eq1513188 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1513188
  have eq1513252 : (M.op (σ x) (σ y)) = (k (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1513231
       have i₂ := eq178
       grind)
    | exact superpose eq178 eq1513231
    | exact resolve eq1513231 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq1513231
  have eq1513267 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1513252
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1513252
    | exact resolve eq1513252 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513252
  have eq1513268 : (M.op (σ x) (σ y)) = (k (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1513267
  have eq1619147 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq193541
       have i₂ := eq182397
       grind)
    | exact superpose eq182397 eq193541
    | exact resolve eq193541 eq182397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182397 eq193541
  have eq1619416 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq1619147
  have eq1619450 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1619416
    | exact resolve eq1619416 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1619416
  have eq1619495 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1619450 eq1513268
    | exact resolve eq1513268 eq1619450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513268 eq1619450
  have eq1619523 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1619495
       have r₂ := eq27
       grind)
    | exact resolve eq1619495 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1619495
  have eq1619531 : (M.op (σ y) (σ y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1619523 eq65
    | exact resolve eq65 eq1619523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1619585 : (M.op (σ y) (σ y)) = (M.op x (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq25907 eq1619531
    | exact resolve eq1619531 eq25907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25907 eq1619531
  have eq1619613 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq31660 eq1619585
    | exact resolve eq1619585 eq31660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1619585
  have eq1619801 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1619613 eq1619523
    | exact resolve eq1619523 eq1619613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1619523 eq1619613
  have eq1619846 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1619801
  have eq1619904 : (M.op y y) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq65 y y
       have i₂ := eq1619846
       grind)
    | exact superpose eq1619846 eq65
    | exact resolve eq65 eq1619846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq1619962 : (M.op y y) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq206 eq1619904
    | exact resolve eq1619904 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq1619904
  have eq1619995 : (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28352 eq1619962
    | exact resolve eq1619962 eq28352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28352 eq1619962
  have eq1622812 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1619846
       have i₂ := eq1619995
       grind)
    | exact superpose eq1619995 eq1619846
    | exact resolve eq1619846 eq1619995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1619846 eq1619995
  have eq1622856 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1622812
  have eq1622953 : (τ (σ y)) = (M.op x (τ (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1622856 eq57569
    | exact resolve eq57569 eq1622856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57569 eq1622856
  have eq1623206 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq1622953
    | exact resolve eq1622953 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1622953
  have eq1623223 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1623206
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1623206
    | exact resolve eq1623206 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1623206
  have eq1623224 : y = (M.op x y) := by grind
  clear eq1623223
  have eq1623236 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1623224 eq20
    | exact resolve eq20 eq1623224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1623224
  have eq1623686 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1623236
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1623236
    | exact resolve eq1623236 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1623236
  have eq1623888 : (M.op (σ x) (σ y)) = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq1623686 eq31660
    | exact resolve eq31660 eq1623686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31660 eq1623686
  have eq1623940 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29359 eq1623888
    | exact resolve eq1623888 eq29359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29359 eq1623888
  have eq1624024 : False := by grind
  exact eq1624024

/-- `Equation4429`: `x ◇ (x ◇ y) = (z ◇ w) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_x_x_pxy_Equation4429 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4429 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4429.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X2) := by
    intro X0 X1 X2 X3
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq13 X0 (k (M.op X0 X0) X1)
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
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
  clear eq40
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq45
    | exact resolve eq45 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 : G, (k x (k y X0)) = (τ (k (σ x) (k (σ y) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq45 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq45
    | exact resolve eq45 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq45 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq45
    | (have j0 := eq45 y
       grind)
    | exact resolve eq45 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (k y (k y X0)) = (τ (k (σ y) (k (σ y) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq48 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq48
    | exact resolve eq48 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq48
  have eq125 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq143 : ∀ X0 : G, (k (k x X0) x) = (τ (k (k (σ x) (σ X0)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq60
    | exact resolve eq60 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq60
  have eq175 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq38 (M.op sF0 sF0)
       have i₂ := eq175 sF0
       grind)
    | exact superpose eq175 eq38
    | exact resolve eq38 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq179 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq20 eq178
    | exact resolve eq178 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq189 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq91 (M.op sF2 sF2)
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq91
    | exact resolve eq91 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq30 eq189
    | exact resolve eq189 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq207 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq108 (M.op sF3 sF3)
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq108
    | exact resolve eq108 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq175
  have eq218 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq32 eq207
    | exact resolve eq207 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq336 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq336 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq336
    | exact resolve eq336 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X0 X1 X2 : G, (k (τ X2) (k (τ X0) X1)) = (τ (k X2 (k X0 (σ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq336 X2 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq336
    | exact resolve eq336 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : ∀ X0 : G, (τ (k (k (σ x) (σ y)) X0)) = (k (k x y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq99 eq427
    | exact resolve eq427 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq427
  have eq688 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 X5) X4) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 X2 (M.op X2 x) X4 X5
       have i₂ := eq16 X2 x X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X0) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X2 X3 X4 (M.op X4 x)
       have i₂ := eq16 X4 x X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 X1 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq694 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 x x
       have i₂ := eq16 X2 X3 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697 : ∀ X0 X1 X4 : G, (M.op (M.op (M.op X0 X1) X0) X4) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq691 X0 X1 x x X4
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq691
    | exact resolve eq691 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq700 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq693 X0 (M.op X0 x)
       have i₂ := eq693 X0 x
       grind)
    | exact superpose eq693 eq693
    | exact resolve eq693 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : ∀ X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op x y) x) := by
    intro X2 X3
    first
    | (have i₁ := eq16 x x X2 X3
       have i₂ := eq693 x x
       grind)
    | exact superpose eq693 eq16
    | exact resolve eq16 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op x y) x) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2 (M.op X2 x)
       have i₂ := eq693 X2 x
       grind)
    | exact superpose eq693 eq16
    | exact resolve eq16 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op X0 (M.op (M.op x y) x)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op X0 x) X2 X3
       have i₂ := eq693 X0 x
       grind)
    | exact superpose eq693 eq16
    | exact resolve eq16 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : ∀ X2 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op x y) x) X2) := by
    intro X2
    first
    | (have i₁ := eq707 x x X2
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq707
    | exact resolve eq707 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq728 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq693 x x
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq693
    | exact resolve eq693 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq731 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2 (M.op X2 x)
       have i₂ := eq694 X2 x
       grind)
    | exact superpose eq694 eq16
    | exact resolve eq16 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq734 : ∀ X2 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X2) := by
    intro X2
    first
    | (have i₁ := eq731 x x X2
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq731
    | exact resolve eq731 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694 eq731
  have eq745 : ∀ X2 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) X2) := by
    intro X2
    first
    | exact superpose eq728 eq734
    | exact resolve eq734 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq756 : ∀ X0 : G, (M.op (M.op x y) x) ≠ (M.op (M.op x y) x) ∨ (k X0 (M.op (M.op x y) x)) = X0 := by
    intro X0
    first
    | exact superpose eq700 eq28
    | (have j0 := eq28 X0 (M.op (M.op x y) x)
       grind)
    | (have r₁ := eq28 X0 (M.op (M.op x y) x)
       have r₂ := eq700 (M.op (M.op x y) x)
       grind)
    | exact resolve eq28 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq763 : ∀ X0 : G, (k X0 (M.op (M.op x y) x)) = X0 := by
    intro X0
    first
    | (have j0 := eq756 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq767 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op x y) x))) := by
    intro X0
    first
    | exact superpose eq763 eq35
    | exact resolve eq35 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq780 : ∀ X0 : G, (k X0 (σ (M.op (M.op x y) x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq767 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq767
    | exact resolve eq767 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq793 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq28
    | (have j0 := eq28 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq28 X0 (M.op X0 X0)
       have r₂ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq796 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op X0 (k X0 X1)) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq693 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq693
    | (have j1 := eq11 X1 X1
       grind)
    | exact resolve eq693 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq806 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
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
  have eq814 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq820 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq821 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq820 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820
  have eq832 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq793 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793
  have eq848 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq832 X0 X1
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq832 X1 X1
       have r₂ := eq28 X1 X1
       grind)
    | (have r₁ := eq832 X1 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq832 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq909 : (σ (M.op (M.op x y) x)) ≠ (σ (M.op (M.op x y) x)) ∨ (σ (M.op (M.op x y) x)) = (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) := by
    first
    | exact superpose eq780 eq821
    | (have j0 := eq821 (σ (M.op (M.op x y) x))
       grind)
    | (have r₁ := eq821 (σ (M.op (M.op x y) x))
       have r₂ := eq780 (σ (M.op (M.op x y) x))
       grind)
    | exact resolve eq821 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq922 : (σ (M.op (M.op x y) x)) = (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) := by grind
  clear eq909
  have eq1004 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (M.op x y) x) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) = X0 := by
    intro X0
    first
    | exact superpose eq709 eq11
    | (have j0 := eq11 X0 X0
       grind)
    | exact resolve eq11 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq1014 : ∀ X0 : G, (M.op (M.op x y) x) = (k (M.op (M.op x y) x) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) = X0 := by
    intro X0
    first
    | exact superpose eq728 eq1004
    | (have j0 := eq1004 X0
       grind)
    | exact resolve eq1004 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq1020 : ∀ X0 : G, (M.op (M.op x y) x) = (k (M.op (M.op x y) x) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1014 X0
       have j1 := eq13 (M.op (M.op x y) x) X0
       grind)
    | (have r₁ := eq1014 x
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq1014 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | (have r₁ := eq1014 x
       have r₂ := eq13 (M.op (M.op x y) x) x
       grind)
    | exact resolve eq1014 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq1023 : ∀ X0 : G, (M.op (M.op x y) x) = (k (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | (have j0 := eq1020 X0
       have j1 := eq28 (M.op (M.op x y) x) X0
       grind)
    | (have r₁ := eq1020 x
       have r₂ := eq28 X0 x
       grind)
    | exact resolve eq1020 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1076 : (σ (M.op (M.op x y) x)) = (k (σ (M.op (M.op x y) x)) (σ (M.op x y))) := by
    first
    | exact superpose eq1023 eq42
    | exact resolve eq42 eq1023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq3077 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq806
       grind)
    | exact superpose eq806 eq41
    | exact resolve eq41 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3078 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3077
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3077
    | exact resolve eq3077 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3077
  have eq3080 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq3078
    | exact resolve eq3078 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3078
  have eq20008 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) x)) = (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) := by
    intro X0
    first
    | exact superpose eq922 eq708
    | exact resolve eq708 eq922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq20012 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) x)) = (σ (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq922 eq20008
    | exact resolve eq20008 eq922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922 eq20008
  have eq20027 : (M.op (M.op x y) x) = (σ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq700 eq20012
    | exact resolve eq20012 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700 eq20012
  have eq20081 : (M.op (M.op x y) x) = (τ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq20027 eq15
    | exact resolve eq15 eq20027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23596 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq3080 eq814
    | exact resolve eq814 eq3080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3080
  have eq23604 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq23596
       have r₂ := eq27
       grind)
    | exact resolve eq23596 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23596
  have eq23611 : y = (k y (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23604 eq218
    | exact resolve eq218 eq23604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq23604
  have eq23644 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq23611
    | exact resolve eq23611 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23611
  have eq23655 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq23644
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq23644
       have r₂ := eq13 y y
       grind)
    | (have r₁ := eq23644
       have r₂ := eq13 x y
       grind)
    | exact resolve eq23644 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23644
  have eq23662 : x = (k x (τ (σ y))) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23655 eq200
    | exact resolve eq200 eq23655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq23655
  have eq23696 : x = (k x y) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq23662
    | exact resolve eq23662 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23662
  have eq23703 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq848 y x
       grind)
    | (have r₁ := eq23696
       have r₂ := eq848 y x
       grind)
    | exact resolve eq23696 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23696
  have eq23706 : x = (k x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq23703
       have r₂ := eq13 x y
       grind)
    | exact resolve eq23703 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23703
  have eq23710 : y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq806
       have i₂ := eq23706
       grind)
    | exact superpose eq23706 eq806
    | exact resolve eq806 eq23706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq23712 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq23706
       grind)
    | exact superpose eq23706 eq41
    | exact resolve eq41 eq23706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq23714 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq23712
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23712
    | exact resolve eq23712 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23712
  have eq23724 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23714 eq814
    | exact resolve eq814 eq23714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq23738 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq28 X0 y
       have i₂ := eq23710
       grind)
    | exact superpose eq23710 eq28
    | (have j0 := eq28 X0 y
       grind)
    | (have r₁ := eq28 X0 y
       have r₂ := eq23710
       grind)
    | exact resolve eq28 eq23710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23741 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op X2 (M.op y y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq688 y y X2 X0 X1
       have i₂ := eq23710
       grind)
    | exact superpose eq23710 eq688
    | exact resolve eq688 eq23710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23748 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op y y) X0) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq697 y y X0
       have i₂ := eq23710
       grind)
    | exact superpose eq23710 eq697
    | exact resolve eq697 eq23710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23751 : (M.op y y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq706 y y
       have i₂ := eq23710
       grind)
    | exact superpose eq23710 eq706
    | exact resolve eq706 eq23710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23754 : ∀ X0 : G, y = (M.op x x) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq23738 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23738
  have eq23757 : y = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23710 eq23751
    | exact resolve eq23751 eq23710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23751
  have eq23760 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op y y) X0) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq728 eq23748
    | exact resolve eq23748 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23748
  have eq23767 : ∀ X2 : G, (M.op (M.op x y) x) = (M.op X2 (M.op y y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X2
    first
    | (have i₁ := eq23741 x x X2
       have i₂ := eq706 x x
       grind)
    | (have i₁ := eq23741 x y X2
       have i₂ := eq706 X2 x
       grind)
    | exact superpose eq706 eq23741
    | (have j0 := eq23741 x y X2
       grind)
    | exact resolve eq23741 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23741
  have eq23772 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op y X0) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq23710 eq23760
    | exact resolve eq23760 eq23710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23760
  have eq23778 : ∀ X2 : G, (M.op (M.op x y) x) = (M.op X2 y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X2
    first
    | exact superpose eq23710 eq23767
    | exact resolve eq23767 eq23710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23710 eq23767
  have eq23780 : ∀ X0 : G, y = (M.op y X0) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq23757 eq23772
    | exact resolve eq23772 eq23757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23772
  have eq23783 : ∀ X2 : G, y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op X2 y) := by
    intro X2
    first
    | exact superpose eq23757 eq23778
    | exact resolve eq23778 eq23757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23778
  have eq23838 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq23724 eq28
    | (have j0 := eq28 X0 (σ y)
       grind)
    | (have r₁ := eq28 X0 (σ y)
       have r₂ := eq23724
       grind)
    | exact resolve eq28 eq23724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23841 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op X2 (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0 X1 X2
    first
    | exact superpose eq23724 eq688
    | exact resolve eq688 eq23724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23848 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ y) (σ y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq23724 eq697
    | exact resolve eq697 eq23724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq23851 : (M.op (σ y) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23724 eq706
    | exact resolve eq706 eq23724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23854 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq23838 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23838
  have eq23857 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq23724 eq23851
    | exact resolve eq23851 eq23724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23851
  have eq23860 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op (σ y) (σ y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq728 eq23848
    | exact resolve eq23848 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23848
  have eq23867 : ∀ X2 : G, (M.op (M.op x y) x) = (M.op X2 (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X2
    first
    | (have i₁ := eq23841 x x X2
       have i₂ := eq706 x x
       grind)
    | (have i₁ := eq23841 x y X2
       have i₂ := eq706 X2 x
       grind)
    | exact superpose eq706 eq23841
    | (have j0 := eq23841 x y X2
       grind)
    | exact resolve eq23841 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23841
  have eq23872 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq23724 eq23860
    | exact resolve eq23860 eq23724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23860
  have eq23878 : ∀ X2 : G, (M.op (M.op x y) x) = (M.op X2 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X2
    first
    | exact superpose eq23724 eq23867
    | exact resolve eq23867 eq23724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23724 eq23867
  have eq23880 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq23857 eq23872
    | exact resolve eq23872 eq23857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23872
  have eq23883 : ∀ X2 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op X2 (σ y)) := by
    intro X2
    first
    | exact superpose eq23857 eq23878
    | exact resolve eq23878 eq23857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23878
  have eq23895 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq693 x x
       have i₂ := eq23754 X0
       grind)
    | exact superpose eq23754 eq693
    | (have j1 := eq23754 X0
       grind)
    | exact resolve eq693 eq23754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23754
  have eq23915 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq23895 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23895
    | (have j0 := eq23895 X0
       grind)
    | exact resolve eq23895 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23895
  have eq24006 : y = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23757 eq20027
    | exact resolve eq20027 eq23757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24036 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq24006
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24006
    | exact resolve eq24006 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24006
  have eq24180 : y = (k x x) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq24036
       grind)
    | exact superpose eq24036 eq11
    | exact resolve eq11 eq24036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24185 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq693 x x
       have i₂ := eq24036
       grind)
    | exact superpose eq24036 eq693
    | exact resolve eq693 eq24036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24196 : y = (k x x) ∨ x = y ∨ x = (M.op x y) ∨ y = (σ y) := by grind
  clear eq24180
  have eq24205 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq24185
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24185
    | exact resolve eq24185 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24185
  have eq24226 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq24205 eq745
    | exact resolve eq745 eq24205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24299 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq24205 eq20027
    | exact resolve eq20027 eq24205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24334 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq24299
    | exact resolve eq24299 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24299
  have eq26463 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq693 x x
       have i₂ := eq23783 X0
       grind)
    | exact superpose eq23783 eq693
    | (have j1 := eq23783 X0
       grind)
    | exact resolve eq693 eq23783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23783
  have eq26486 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq26463 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq26463
    | (have j0 := eq26463 X0
       grind)
    | exact resolve eq26463 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26463
  have eq26500 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq24205 eq26486
    | exact resolve eq26486 eq24205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26486
  have eq28735 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq693 X0 x
       have i₂ := eq23854 (M.op X0 x)
       grind)
    | exact superpose eq23854 eq693
    | (have j1 := eq23854 X0
       grind)
    | exact resolve eq693 eq23854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23854
  have eq28756 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq28735
    | (have j0 := eq28735 X0
       grind)
    | exact resolve eq28735 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28735
  have eq28780 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq23857 eq693
    | exact resolve eq693 eq23857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23857
  have eq28801 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq26 eq28780
    | exact resolve eq28780 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28780
  have eq28972 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq23883 eq693
    | (have j1 := eq23883 X0
       grind)
    | exact resolve eq693 eq23883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693 eq23883
  have eq28993 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq28972
    | (have j0 := eq28972 X0
       grind)
    | exact resolve eq28972 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28972
  have eq29022 : ∀ X0 X1 : G, (k X0 (σ (M.op x y))) = X0 ∨ x = (M.op x y) ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq780 X0
       have i₂ := eq23915 (M.op sF0 x)
       grind)
    | exact superpose eq23915 eq780
    | (have j1 := eq23915 X1
       grind)
    | exact resolve eq780 eq23915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq29039 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq1076
       have i₂ := eq23915 (M.op sF0 x)
       grind)
    | exact superpose eq23915 eq1076
    | (have j1 := eq23915 X0
       grind)
    | exact resolve eq1076 eq23915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq29086 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq20027
       have i₂ := eq23915 (M.op sF0 x)
       grind)
    | exact superpose eq23915 eq20027
    | (have j1 := eq23915 X0
       grind)
    | exact resolve eq20027 eq23915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23915
  have eq29127 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq29086
    | (have j0 := eq29086 X0
       grind)
    | exact resolve eq29086 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29086
  have eq29152 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq29039
    | (have j0 := eq29039 X0
       grind)
    | exact resolve eq29039 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29039
  have eq29162 : ∀ X0 X1 : G, (k X1 y) = X1 ∨ x = (M.op x y) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq20 eq29022
    | (have j0 := eq29022 X0 X1
       grind)
    | exact resolve eq29022 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29022
  have eq29183 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq24334 eq29127
    | exact resolve eq29127 eq24334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24334 eq29127
  have eq29208 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq29183 eq821
    | (have j0 := eq821 (σ y)
       grind)
    | (have r₁ := eq821 (σ y)
       have r₂ := eq29183 (σ y)
       grind)
    | exact resolve eq821 eq29183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29183
  have eq29287 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq29208
  have eq29867 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op X2 (M.op (σ y) (σ y))) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq29287 eq688
    | exact resolve eq688 eq29287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29877 : (M.op (σ y) (σ y)) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq29287 eq706
    | exact resolve eq706 eq29287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29884 : (σ y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq29287 eq29877
    | exact resolve eq29877 eq29287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29877
  have eq29894 : ∀ X2 : G, (M.op (M.op x y) x) = (M.op X2 (M.op (σ y) (σ y))) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X2
    first
    | (have i₁ := eq29867 x x X2
       have i₂ := eq706 x x
       grind)
    | (have i₁ := eq29867 x y X2
       have i₂ := eq706 X2 x
       grind)
    | exact superpose eq706 eq29867
    | (have j0 := eq29867 x y X2
       grind)
    | exact resolve eq29867 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29867
  have eq29905 : ∀ X2 : G, (M.op (M.op x y) x) = (M.op X2 (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X2
    first
    | exact superpose eq29287 eq29894
    | exact resolve eq29894 eq29287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29287 eq29894
  have eq29911 : ∀ X2 : G, (σ y) = (M.op X2 (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X2
    first
    | exact superpose eq29884 eq29905
    | exact resolve eq29905 eq29884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29884 eq29905
  have eq30711 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq29911 eq26
    | (have j1 := eq29911 (σ x)
       grind)
    | exact resolve eq26 eq29911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29911
  have eq30783 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq30711 eq27
    | exact resolve eq27 eq30711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30711
  have eq33127 : (σ y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq26500 eq745
    | exact resolve eq745 eq26500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq33136 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26500 eq26
    | (have j1 := eq26500 (σ x)
       grind)
    | exact resolve eq26 eq26500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26500
  have eq33291 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33136 eq23757
    | exact resolve eq23757 eq33136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23757 eq33136
  have eq33315 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq33291
  have eq33333 : y = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24036 eq33315
    | exact resolve eq33315 eq24036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24036 eq33315
  have eq41202 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq20027
       have i₂ := eq28756 (M.op sF0 x)
       grind)
    | exact superpose eq28756 eq20027
    | (have j1 := eq28756 X0
       grind)
    | exact resolve eq20027 eq28756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28756
  have eq41489 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq41202 eq821
    | (have j0 := eq821 (σ y)
       grind)
    | (have r₁ := eq821 (σ y)
       have r₂ := eq41202 (σ y)
       grind)
    | exact resolve eq821 eq41202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41202
  have eq41572 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) := by grind
  clear eq41489
  have eq41880 : (M.op (σ y) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq41572 eq706
    | exact resolve eq706 eq41572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41887 : (σ y) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq41572 eq41880
    | exact resolve eq41880 eq41572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41572 eq41880
  have eq42453 : (σ y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq41887 eq20081
    | exact resolve eq20081 eq41887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41887
  have eq42501 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq32 eq42453
    | exact resolve eq42453 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42453
  have eq42708 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq42501 eq15
    | exact resolve eq15 eq42501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42501
  have eq45764 : ∀ X0 : G, (σ y) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq28801 eq763
    | exact resolve eq763 eq28801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46894 : ∀ X0 X1 : G, (σ y) = (M.op X1 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq28993 eq763
    | (have j1 := eq28993 X1
       grind)
    | exact resolve eq763 eq28993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763 eq28993
  have eq48576 : ∀ X0 : G, y ≠ y ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq821 y
       have i₂ := eq29162 X0 y
       grind)
    | exact superpose eq29162 eq821
    | (have j0 := eq821 y
       have j1 := eq29162 X0 x
       grind)
    | (have r₁ := eq821 y
       have r₂ := eq29162 X0 y
       grind)
    | (have r₁ := eq821 (σ (M.op x y))
       have r₂ := eq29162 (σ (M.op x y)) x
       grind)
    | exact resolve eq821 eq29162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29162
  have eq48642 : ∀ X0 : G, y = (M.op y y) ∨ x = (M.op x y) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq48576 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48576
  have eq50231 : (M.op x y) ≠ (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) := by grind
  have eq61060 : ∀ X0 : G, (σ y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq20081
       have i₂ := eq45764 (M.op sF0 x)
       grind)
    | exact superpose eq45764 eq20081
    | (have j1 := eq45764 X0
       grind)
    | exact resolve eq20081 eq45764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45764
  have eq61134 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq32 eq61060
    | (have j0 := eq61060 X0
       grind)
    | exact resolve eq61060 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61060
  have eq61383 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq61134 eq821
    | (have j0 := eq821 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq821 (M.op (σ x) (σ y))
       have r₂ := eq61134 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq821 eq61134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61134
  have eq61442 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq61383
  have eq61569 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq61442 eq706
    | exact resolve eq706 eq61442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61577 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq61442 eq61569
    | exact resolve eq61569 eq61442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61442 eq61569
  have eq61729 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq61577 eq24226
    | exact resolve eq24226 eq61577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24226 eq61577
  have eq61756 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq61729
  have eq65946 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq46894 (M.op sF2 sF3) x
       grind)
    | exact superpose eq46894 eq26
    | (have j1 := eq46894 X0 (σ x)
       grind)
    | exact resolve eq26 eq46894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46894
  have eq66044 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq65946 eq821
    | (have j0 := eq821 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq821 (M.op (σ x) (σ y))
       have r₂ := eq65946 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq821 eq65946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65946
  have eq66105 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq66044
  have eq66222 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq66105 eq688
    | exact resolve eq688 eq66105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66232 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq66105 eq706
    | exact resolve eq706 eq66105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66240 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq66105 eq66232
    | exact resolve eq66232 eq66105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66232
  have eq66249 : ∀ X2 : G, (M.op (M.op x y) x) = (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | (have i₁ := eq66222 x x X2
       have i₂ := eq706 x x
       grind)
    | (have i₁ := eq66222 x y X2
       have i₂ := eq706 X2 x
       grind)
    | exact superpose eq706 eq66222
    | (have j0 := eq66222 x y X2
       grind)
    | exact resolve eq66222 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66222
  have eq66259 : ∀ X2 : G, (M.op (M.op x y) x) = (M.op X2 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq66105 eq66249
    | exact resolve eq66249 eq66105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66105 eq66249
  have eq66264 : ∀ X2 : G, (M.op (σ x) (σ y)) = (M.op X2 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq66240 eq66259
    | exact resolve eq66259 eq66240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66259
  have eq66946 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq66264 eq23880
    | exact resolve eq23880 eq66264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23880 eq66264
  have eq66967 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq66946
  have eq67172 : ∀ X0 : G, (σ y) ≠ X0 ∨ (σ x) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq66967 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq66967
       grind)
    | exact resolve eq13 eq66967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67173 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq66967 eq11
    | exact resolve eq11 eq66967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67190 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq67173
  have eq69003 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op X2 (M.op y y)) ∨ x = (M.op x y) ∨ (k X3 (σ (M.op x y))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq688 y y X2 X0 X1
       have i₂ := eq48642 X3
       grind)
    | exact superpose eq48642 eq688
    | (have j1 := eq48642 X3
       grind)
    | exact resolve eq688 eq48642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69013 : ∀ X0 : G, (M.op y y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq706 y y
       have i₂ := eq48642 X0
       grind)
    | exact superpose eq48642 eq706
    | (have j1 := eq48642 X0
       grind)
    | exact resolve eq706 eq48642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69020 : ∀ X0 : G, y = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq48642 eq69013
    | (have j0 := eq69013 X0
       have j1 := eq48642 X0
       grind)
    | exact resolve eq69013 eq48642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69013
  have eq69030 : ∀ X2 X3 : G, (M.op (M.op x y) x) = (M.op X2 (M.op y y)) ∨ x = (M.op x y) ∨ (k X3 (σ (M.op x y))) = X3 := by
    intro X2 X3
    first
    | (have i₁ := eq69003 x x X2 X3
       have i₂ := eq706 x x
       grind)
    | (have i₁ := eq69003 x y X2 X3
       have i₂ := eq706 X2 X3
       grind)
    | exact superpose eq706 eq69003
    | (have j0 := eq69003 x y X2 X3
       grind)
    | exact resolve eq69003 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69003
  have eq69041 : ∀ X2 X3 : G, (M.op (M.op x y) x) = (M.op X2 y) ∨ x = (M.op x y) ∨ (k X3 (σ (M.op x y))) = X3 := by
    intro X2 X3
    first
    | exact superpose eq48642 eq69030
    | (have j0 := eq69030 X2 X3
       have j1 := eq48642 X3
       grind)
    | exact resolve eq69030 eq48642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48642 eq69030
  have eq69047 : ∀ X2 X3 : G, y = (M.op X2 y) ∨ x = (M.op x y) ∨ (k X3 (σ (M.op x y))) = X3 := by
    intro X2 X3
    first
    | exact superpose eq69020 eq69041
    | (have j0 := eq69041 X2 X3
       have j1 := eq69020 X3
       grind)
    | exact resolve eq69041 eq69020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69041
  have eq74705 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ x = (M.op x y) ∨ y = (τ y) := by
    intro X0
    first
    | (have i₁ := eq20081
       have i₂ := eq69020 (M.op sF0 x)
       grind)
    | exact superpose eq69020 eq20081
    | (have j1 := eq69020 X0
       grind)
    | exact resolve eq20081 eq69020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20081 eq69020
  have eq75007 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (τ y) := by
    first
    | exact superpose eq74705 eq821
    | (have j0 := eq821 (σ (M.op x y))
       grind)
    | (have r₁ := eq821 (σ (M.op x y))
       have r₂ := eq74705 (σ (M.op x y))
       grind)
    | exact resolve eq821 eq74705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74705
  have eq75096 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (τ y) := by grind
  clear eq75007
  have eq75291 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (τ y) := by
    first
    | exact superpose eq75096 eq706
    | exact resolve eq706 eq75096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75301 : (σ (M.op x y)) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (τ y) := by
    first
    | exact superpose eq75096 eq75291
    | exact resolve eq75291 eq75096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75096 eq75291
  have eq75492 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (τ y) := by
    first
    | exact superpose eq75301 eq66240
    | exact resolve eq66240 eq75301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75301
  have eq75561 : y = (τ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq75492
       have r₂ := eq27
       grind)
    | exact resolve eq75492 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75492
  have eq77487 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq69047 x X0
       grind)
    | exact superpose eq69047 eq18
    | (have j1 := eq69047 x X0
       grind)
    | exact resolve eq18 eq69047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69047
  have eq77646 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq77487 eq821
    | (have j0 := eq821 (σ (M.op x y))
       grind)
    | (have r₁ := eq821 (σ (M.op x y))
       have r₂ := eq77487 (σ (M.op x y))
       grind)
    | exact resolve eq821 eq77487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77720 : (τ (σ (M.op x y))) = (k (M.op x y) (τ (σ (M.op x y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq77487 eq125
    | exact resolve eq125 eq77487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq77487
  have eq77735 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq77646
  have eq77745 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq77720
    | exact resolve eq77720 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77720
  have eq77858 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op X2 (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq77735 eq688
    | exact resolve eq688 eq77735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77868 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq77735 eq706
    | exact resolve eq706 eq77735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77878 : (σ (M.op x y)) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq77735 eq77868
    | exact resolve eq77868 eq77735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77868
  have eq77888 : ∀ X2 : G, (M.op (M.op x y) x) = (M.op X2 (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X2
    first
    | (have i₁ := eq77858 x x X2
       have i₂ := eq706 x x
       grind)
    | (have i₁ := eq77858 x y X2
       have i₂ := eq706 X2 x
       grind)
    | exact superpose eq706 eq77858
    | (have j0 := eq77858 x y X2
       grind)
    | exact resolve eq77858 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77858
  have eq77903 : ∀ X2 : G, (M.op (M.op x y) x) = (M.op X2 (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X2
    first
    | exact superpose eq77735 eq77888
    | exact resolve eq77888 eq77735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77735 eq77888
  have eq77910 : ∀ X2 : G, (σ (M.op x y)) = (M.op X2 (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X2
    first
    | exact superpose eq77878 eq77903
    | exact resolve eq77903 eq77878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77903
  have eq78204 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq33127 eq77878
    | exact resolve eq77878 eq33127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78321 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq77878 eq28801
    | exact resolve eq28801 eq77878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78326 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq77878 eq33127
    | exact resolve eq33127 eq77878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33127
  have eq78344 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq77878 eq66240
    | exact resolve eq66240 eq77878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66240 eq77878
  have eq78381 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq78326
  have eq78395 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) := by grind
  clear eq78204
  have eq78415 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq78344
       have r₂ := eq27
       grind)
    | exact resolve eq78344 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78344
  have eq78428 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq78381
       have r₂ := eq30783
       grind)
    | exact resolve eq78381 eq30783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78381
  have eq78433 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq78321
       have r₂ := eq27
       grind)
    | exact resolve eq78321 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78321
  have eq78512 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq24205 eq78395
    | exact resolve eq78395 eq24205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24205 eq78395
  have eq78535 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq78428 eq78433
    | exact resolve eq78433 eq78428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78433
  have eq78553 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq78512
       have r₂ := eq50231
       grind)
    | exact resolve eq78512 eq50231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50231 eq78512
  have eq80246 : y = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq77910 y
       have i₂ := eq23780 sF1
       grind)
    | exact superpose eq23780 eq77910
    | exact resolve eq77910 eq23780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23780 eq77910
  have eq80371 : y = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq80246
  have eq80423 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq78428 eq80371
    | exact resolve eq80371 eq78428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78428 eq80371
  have eq80424 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq80423
  have eq81049 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq78553 eq20027
    | exact resolve eq20027 eq78553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20027 eq78553
  have eq81139 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq81049
    | exact resolve eq81049 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81049
  have eq81231 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq81139
       have r₂ := eq30783
       grind)
    | exact resolve eq81139 eq30783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30783 eq81139
  have eq81276 : (M.op x y) = (τ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq81231 eq29
    | exact resolve eq29 eq81231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq81342 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (k X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq81231 eq29152
    | (have j0 := eq29152 X0
       grind)
    | exact resolve eq29152 eq81231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29152
  have eq81390 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq81342 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81342
  have eq81408 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq77745 eq81390
    | exact resolve eq81390 eq77745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77745 eq81390
  have eq81451 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq81408 X0
       have j1 := eq848 (M.op x y) X0
       grind)
    | (have r₁ := eq81408 X0
       have r₂ := eq848 (M.op x y) x
       grind)
    | (have r₁ := eq81408 (M.op x y)
       have r₂ := eq848 (M.op x y) x
       grind)
    | exact resolve eq81408 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848 eq81408
  have eq81593 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq81451 eq821
    | (have j0 := eq821 (M.op x y)
       grind)
    | (have r₁ := eq821 (M.op x y)
       have r₂ := eq81451 (M.op x y)
       grind)
    | exact resolve eq821 eq81451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81665 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq81593
  have eq81840 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op X2 (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq81665 eq688
    | exact resolve eq688 eq81665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq81850 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq81665 eq706
    | exact resolve eq706 eq81665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81861 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq81665 eq81850
    | exact resolve eq81850 eq81665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81850
  have eq81871 : ∀ X2 : G, (M.op (M.op x y) x) = (M.op X2 (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    intro X2
    first
    | (have i₁ := eq81840 x x X2
       have i₂ := eq706 x x
       grind)
    | (have i₁ := eq81840 x y X2
       have i₂ := eq706 X2 x
       grind)
    | exact superpose eq706 eq81840
    | (have j0 := eq81840 x y X2
       grind)
    | exact resolve eq81840 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706 eq81840
  have eq81882 : ∀ X2 : G, (M.op (M.op x y) x) = (M.op X2 (M.op x y)) ∨ x = (M.op x y) := by
    intro X2
    first
    | exact superpose eq81665 eq81871
    | exact resolve eq81871 eq81665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81665 eq81871
  have eq81888 : ∀ X2 : G, (M.op x y) = (M.op X2 (M.op x y)) ∨ x = (M.op x y) := by
    intro X2
    first
    | exact superpose eq81861 eq81882
    | exact resolve eq81882 eq81861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81882
  have eq81947 : ∀ X0 : G, (M.op x y) = (k (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq81861 eq1023
    | exact resolve eq1023 eq81861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023
  have eq83747 : y = (k x x) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq80424
       grind)
    | exact superpose eq80424 eq11
    | exact resolve eq11 eq80424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80424
  have eq83764 : y = (k x x) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq83747
  have eq88473 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq78415 eq27
    | exact resolve eq27 eq78415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78415
  have eq88551 : (M.op x y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq81231 eq88473
    | exact resolve eq88473 eq81231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88473
  have eq88563 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq88551
       have r₂ := eq78535
       grind)
    | exact resolve eq88551 eq78535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88551
  have eq88574 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq88563 eq27
    | exact resolve eq27 eq88563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88579 : (M.op (σ x) (σ x)) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq88563 eq728
    | exact resolve eq728 eq88563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88563
  have eq88590 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq81861 eq88579
    | exact resolve eq88579 eq81861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88579
  have eq88594 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq81231 eq88574
    | exact resolve eq88574 eq81231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88574
  have eq88621 : (M.op x y) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq88590 eq11
    | exact resolve eq11 eq88590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88590
  have eq88638 : (M.op x y) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq88621
  have eq88655 : (M.op x y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq88638
       have r₂ := eq88594
       grind)
    | exact resolve eq88638 eq88594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88594 eq88638
  have eq88679 : (k x x) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq88655 eq98
    | exact resolve eq98 eq88655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88655
  have eq88710 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq81276 eq88679
    | exact resolve eq88679 eq81276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88679
  have eq121778 : y = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14 y
       have i₂ := eq75561
       grind)
    | exact superpose eq75561 eq14
    | exact resolve eq14 eq75561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75561
  have eq121863 : y = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq121778
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq121778
    | exact resolve eq121778 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121778
  have eq121891 : y = (σ y) ∨ (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq61756 eq121863
    | exact resolve eq121863 eq61756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61756 eq121863
  have eq121916 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq78535 eq121891
    | exact resolve eq121891 eq78535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78535 eq121891
  have eq121917 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by grind
  clear eq121916
  have eq121953 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq121917 eq27
    | exact resolve eq27 eq121917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121958 : (M.op (σ x) (σ x)) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq121917 eq728
    | exact resolve eq728 eq121917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq121969 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq81861 eq121958
    | exact resolve eq121958 eq81861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81861 eq121958
  have eq121973 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq81231 eq121953
    | exact resolve eq121953 eq81231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121953
  have eq122001 : (M.op x y) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq121969 eq11
    | exact resolve eq11 eq121969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121969
  have eq122018 : (M.op x y) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by grind
  clear eq122001
  have eq122055 : (M.op x y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq122018
       have r₂ := eq121973
       grind)
    | exact resolve eq122018 eq121973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122018
  have eq122076 : (k x x) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq122055 eq98
    | exact resolve eq98 eq122055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122112 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq81276 eq122076
    | exact resolve eq122076 eq81276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122076
  have eq138593 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq88710
       have i₂ := eq24196
       grind)
    | exact superpose eq24196 eq88710
    | exact resolve eq88710 eq24196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24196
  have eq138618 : y = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq138593
  have eq138647 : (σ y) = (σ (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq138618
       grind)
    | exact superpose eq138618 eq24
    | exact resolve eq24 eq138618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138682 : x = (k x (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq23706
       have i₂ := eq138618
       grind)
    | exact superpose eq138618 eq23706
    | exact resolve eq23706 eq138618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138757 : (M.op x y) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by grind
  have eq139802 : (τ (k (k (σ x) (σ y)) (σ x))) = (k (k x (σ y)) x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq138647 eq143
    | exact resolve eq143 eq138647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq138647
  have eq139963 : (k (k x y) (τ (σ x))) = (k (k x (σ y)) x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq604 eq139802
    | exact resolve eq139802 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604 eq139802
  have eq140061 : (k (k x y) x) = (k (k x (σ y)) x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq139963
    | exact resolve eq139963 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq139963
  have eq140137 : (k x x) = (k (k x (σ y)) x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq140061
       have i₂ := eq23706
       grind)
    | exact superpose eq23706 eq140061
    | exact resolve eq140061 eq23706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23706 eq140061
  have eq140190 : y = (k (k x (σ y)) x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq83764 eq140137
    | exact resolve eq140137 eq83764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83764 eq140137
  have eq140211 : (σ y) = (k (k x (σ y)) x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq138618 eq140190
    | exact resolve eq140190 eq138618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138618 eq140190
  have eq140225 : (σ y) = (k x x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq138682 eq140211
    | exact resolve eq140211 eq138682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138682 eq140211
  have eq140236 : (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq88710 eq140225
    | exact resolve eq140225 eq88710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88710 eq140225
  have eq140245 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq140236
       have r₂ := eq138757
       grind)
    | exact resolve eq140236 eq138757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138757 eq140236
  have eq140250 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq140245
       grind)
    | exact superpose eq140245 eq24
    | exact resolve eq24 eq140245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140245
  have eq140410 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq140250
    | exact resolve eq140250 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140250
  have eq140433 : (M.op x y) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq81231 eq140410
    | exact resolve eq140410 eq81231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140410
  have eq140490 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq140433 eq26
    | exact resolve eq26 eq140433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140815 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq81888 eq140490
    | exact resolve eq140490 eq81888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81888 eq140490
  have eq140971 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq140815 eq27
    | exact resolve eq27 eq140815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140815
  have eq141096 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq140971
       have r₂ := eq81231
       grind)
    | exact resolve eq140971 eq81231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81231 eq140971
  have eq150074 : ∀ X0 : G, x ≠ y ∨ (k X0 x) = X0 ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq28 X0 x
       have i₂ := eq33333
       grind)
    | exact superpose eq33333 eq28
    | (have j0 := eq28 X0 x
       grind)
    | exact resolve eq28 eq33333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq33333
  have eq150108 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq150074 X0
       grind)
    | (have r₁ := eq150074 X0
       have r₂ := eq140433
       grind)
    | exact resolve eq150074 eq140433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140433 eq150074
  have eq150119 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq121917 eq150108
    | (have j0 := eq150108 X0
       grind)
    | exact resolve eq150108 eq121917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121917 eq150108
  have eq155103 : x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq122112
       have i₂ := eq150119 x
       grind)
    | exact superpose eq150119 eq122112
    | exact resolve eq122112 eq150119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122112 eq150119
  have eq155124 : (σ x) = (σ y) ∨ (M.op x y) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq155103
  have eq155239 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq155124 eq23714
    | exact resolve eq23714 eq155124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155124
  have eq155434 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122055 eq155239
    | exact resolve eq155239 eq122055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122055 eq155239
  have eq155509 : (M.op x y) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq155434
       have r₂ := eq121973
       grind)
    | exact resolve eq155434 eq121973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121973 eq155434
  have eq155533 : ∀ X0 : G, (k x (k y X0)) = (τ (k (σ x) (k (M.op x y) (σ X0)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq155509 eq93
    | exact resolve eq93 eq155509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq155538 : ∀ X0 : G, (k y (k y X0)) = (τ (k (M.op x y) (k (M.op x y) (σ X0)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq155509 eq110
    | exact resolve eq110 eq155509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq155509
  have eq155855 : ∀ X0 : G, (k y (k y X0)) = (k (τ (M.op x y)) (k (τ (M.op x y)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq155538 x
       have i₂ := eq431 sF0 x sF0
       grind)
    | exact superpose eq431 eq155538
    | exact resolve eq155538 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431 eq155538
  have eq155860 : ∀ X0 : G, (k x (k y X0)) = (k x (τ (k (M.op x y) (σ X0)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq91 eq155533
    | exact resolve eq155533 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq155533
  have eq155930 : ∀ X0 : G, (k y (k y X0)) = (k (M.op x y) (k (M.op x y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq81276 eq155855
    | exact resolve eq155855 eq81276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155855
  have eq155935 : ∀ X0 : G, (k x (k y X0)) = (k x (k (τ (M.op x y)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq155860 x
       have i₂ := eq336 sF0 x
       grind)
    | exact superpose eq336 eq155860
    | exact resolve eq155860 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336 eq155860
  have eq155995 : ∀ X0 : G, (M.op x y) = (k y (k y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq81947 eq155930
    | exact resolve eq155930 eq81947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155930
  have eq156000 : ∀ X0 : G, (k x (k y X0)) = (k x (k (M.op x y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq81276 eq155935
    | exact resolve eq155935 eq81276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81276 eq155935
  have eq156049 : ∀ X0 : G, (M.op x y) = (k x (k x X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq141096 eq155995
    | exact resolve eq155995 eq141096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155995
  have eq156052 : ∀ X0 : G, (k x (M.op x y)) = (k x (k y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq81947 eq156000
    | exact resolve eq156000 eq81947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81947 eq156000
  have eq156090 : ∀ X0 : G, x = (k x (k y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq81451 eq156052
    | exact resolve eq156052 eq81451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81451 eq156052
  have eq156113 : ∀ X0 : G, x = (k x (k x X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq141096 eq156090
    | exact resolve eq156090 eq141096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141096 eq156090
  have eq156129 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq156049 eq156113
    | exact resolve eq156113 eq156049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156049 eq156113
  have eq156130 : x = (M.op x y) := by grind
  clear eq156129
  have eq156140 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq156130
       grind)
    | exact superpose eq156130 eq18
    | exact resolve eq18 eq156130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq156141 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq156130
       grind)
    | exact superpose eq156130 eq22
    | exact resolve eq22 eq156130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq156261 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq28801
       have i₂ := eq156130
       grind)
    | exact superpose eq156130 eq28801
    | exact resolve eq28801 eq156130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28801
  have eq156558 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq156141 eq20
    | exact resolve eq20 eq156141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157333 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq156140 eq695
    | exact resolve eq695 eq156140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq175189 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq156261
  have eq188189 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq67190 eq98
    | exact resolve eq98 eq67190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq188240 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq188189
       have i₂ := eq156130
       grind)
    | exact superpose eq156130 eq188189
    | exact resolve eq188189 eq156130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188189
  have eq188253 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq188240
    | exact resolve eq188240 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188240
  have eq197072 : (M.op (M.op x y) x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq188253 eq796
    | (have j0 := eq796 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq796 eq188253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796 eq188253
  have eq197075 : (M.op (M.op x y) x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq197072
  have eq197105 : (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq156140 eq197075
    | exact resolve eq197075 eq156140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197075
  have eq197121 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq197105
       have i₂ := eq156130
       grind)
    | exact superpose eq156130 eq197105
    | exact resolve eq197105 eq156130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156130 eq197105
  have eq197122 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq197121
  have eq199633 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq197122 eq179
    | exact resolve eq179 eq197122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq197122
  have eq199749 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq199633
    | exact resolve eq199633 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199633
  have eq199756 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq156558 eq199749
    | exact resolve eq199749 eq156558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199749
  have eq199760 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq67172 (σ x)
       grind)
    | (have r₁ := eq199756
       have r₂ := eq67172 (σ x)
       grind)
    | (have r₁ := eq199756
       have r₂ := eq67172 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq199756 eq67172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67172 eq199756
  have eq199775 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq199760 eq67190
    | exact resolve eq67190 eq199760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67190
  have eq199790 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq199760 eq821
    | (have j0 := eq821 (σ x)
       grind)
    | (have r₁ := eq821 (σ x)
       have r₂ := eq199760
       grind)
    | exact resolve eq821 eq199760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821 eq199760
  have eq199812 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq199790
  have eq199814 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq199775
  have eq199863 : (σ y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq199814 eq42708
    | exact resolve eq42708 eq199814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42708 eq199814
  have eq200036 : (σ y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq199863
  have eq200065 : y = (σ y) ∨ (σ x) = (σ y) ∨ y = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq200036
    | exact resolve eq200036 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq200036
  have eq200066 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (σ y) := by grind
  clear eq200065
  have eq200103 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq200066 eq27
    | exact resolve eq27 eq200066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200066
  have eq200137 : (σ x) = (σ y) ∨ y = (σ y) := by
    first
    | (have r₁ := eq200103
       have r₂ := eq156558
       grind)
    | exact resolve eq200103 eq156558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200103
  have eq200144 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (σ y) := by
    first
    | exact superpose eq200137 eq26
    | exact resolve eq26 eq200137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200230 : (σ x) = (k (σ x) (σ x)) ∨ y = (σ y) := by
    first
    | exact superpose eq200137 eq23714
    | exact resolve eq23714 eq200137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23714 eq200137
  have eq201427 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq200144 eq11
    | exact resolve eq11 eq200144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200144
  have eq201446 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq201427
  have eq201471 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq200230 eq201446
    | exact resolve eq201446 eq200230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200230 eq201446
  have eq201472 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq201471
  have eq204686 : (σ (M.op x y)) ≠ (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq201472 eq27
    | exact resolve eq27 eq201472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201472
  have eq204714 : y = (σ y) := by
    first
    | (have r₁ := eq204686
       have r₂ := eq156558
       grind)
    | exact resolve eq204686 eq156558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204686
  have eq204726 : (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq24
       have i₂ := eq204714
       grind)
    | exact superpose eq204714 eq24
    | exact resolve eq24 eq204714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq204855 : (M.op x y) = (M.op (M.op x y) (σ y)) := by
    first
    | (have i₁ := eq156140
       have i₂ := eq204714
       grind)
    | exact superpose eq204714 eq156140
    | exact resolve eq156140 eq204714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156140 eq204714
  have eq217520 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq199812 eq157333
    | exact resolve eq157333 eq199812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199812
  have eq217547 : (σ y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq66967 eq217520
    | exact resolve eq217520 eq66967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66967 eq217520
  have eq217568 : (σ y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq217547
       have r₂ := eq175189
       grind)
    | exact resolve eq217547 eq175189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175189 eq217547
  have eq217791 : (σ y) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq217568 eq157333
    | exact resolve eq157333 eq217568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157333 eq217568
  have eq217821 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq204855 eq217791
    | exact resolve eq217791 eq204855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217791
  have eq218038 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq217821 eq27
    | exact resolve eq27 eq217821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217821
  have eq218066 : (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq218038
       have r₂ := eq156558
       grind)
    | exact resolve eq218038 eq156558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156558 eq218038
  have eq218323 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq218066 eq204726
    | exact resolve eq204726 eq218066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204726 eq218066
  have eq218933 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq218323 eq156141
    | exact resolve eq156141 eq218323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156141
  have eq218934 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq218323 eq20
    | exact resolve eq20 eq218323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq218323
  have eq219968 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq218933 eq26
    | exact resolve eq26 eq218933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq218933
  have eq220295 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq204855 eq219968
    | exact resolve eq219968 eq204855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204855 eq219968
  have eq220857 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq220295 eq27
    | exact resolve eq27 eq220295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq220295
  have eq220993 : False := by grind
  exact eq220993
