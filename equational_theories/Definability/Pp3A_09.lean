import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2306`: `x = (y ◇ (x ◇ (y ◇ z))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_pxy_pyx_pxy_Equation2306 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2306 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2306.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X2))) X0) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
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
  clear eq37
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
  have eq115 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq48 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq48
    | (have j0 := eq48 x
       grind)
    | exact resolve eq48 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq48
    | (have j0 := eq48 (M.op x y)
       grind)
    | exact resolve eq48 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
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
  have eq175 : ∀ X0 : G, (M.op (M.op x (M.op X0 (M.op x y))) X0) = X0 := by
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
  have eq176 : ∀ X0 : G, (M.op (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X0 (M.op X1 X2))) (M.op X3 X0)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op X1 (M.op X0 (M.op X1 X2))) X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq566 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq570 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq547
       grind)
    | exact superpose eq547 eq41
    | exact resolve eq41 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq547
  have eq571 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq570
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq570
    | exact resolve eq570 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq573 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq571
    | exact resolve eq571 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq581 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq573 eq548
    | exact resolve eq548 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq581
       have r₂ := eq27
       grind)
    | exact resolve eq581 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq592 : ∀ X0 : G, (M.op (M.op (σ x) (M.op X0 (σ y))) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq588 eq176
    | exact resolve eq176 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq600 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq592
    | (have j0 := eq592 (σ x)
       grind)
    | exact resolve eq592 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq603 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (M.op X0 (σ y))) (M.op X1 X0)) X1) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq592 eq16
    | exact resolve eq16 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq609 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq588 eq600
    | exact resolve eq600 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq616 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq609
    | exact resolve eq609 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq623 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq588 eq616
    | exact resolve eq616 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq687 : ∀ X0 : G, (M.op x (M.op X0 (M.op x y))) = (M.op (M.op (M.op (σ x) (M.op X0 (σ y))) X0) (M.op x (M.op X0 (M.op x y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq175 eq603
    | exact resolve eq603 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq689 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ y))) = (M.op (M.op (M.op (σ x) (M.op X0 (σ y))) X0) (M.op (σ x) (M.op X0 (σ y)))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq592 eq603
    | exact resolve eq603 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq707 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ y))) = (M.op (M.op (M.op (σ x) (M.op X0 (σ y))) X0) (M.op (σ x) (M.op X0 (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq689 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq719 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ y))) = (M.op X0 (M.op (σ x) (M.op X0 (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq592 eq707
    | exact resolve eq707 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq721 : ∀ X0 : G, (M.op x (M.op X0 (M.op x y))) = (M.op X0 (M.op x (M.op X0 (M.op x y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq592 eq687
    | exact resolve eq687 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq792 : y ≠ (M.op x y) ∨ y = (M.op x x) ∨ (k x y) = (M.op y x) := by
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
  have eq793 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq794 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq623 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq623
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq623
       grind)
    | exact resolve eq12 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq797 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq794
  have eq808 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq797
    | exact resolve eq797 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq816 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq588 eq808
    | exact resolve eq808 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq817 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq566 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq566
    | (have j0 := eq566 (σ X0) (σ X1)
       grind)
    | exact resolve eq566 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq824 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq816 eq142
    | exact resolve eq142 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq816
  have eq826 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq824
    | exact resolve eq824 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq836 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq826 eq179
    | exact resolve eq179 eq826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq847 : (σ x) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq623 eq836
    | exact resolve eq836 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq852 : (τ (σ x)) = (k y (τ (σ x))) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq847 eq108
    | exact resolve eq108 eq847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq847
  have eq859 : y = (k y x) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq852
    | exact resolve eq852 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq1008 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op X0 (σ y))) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq719 eq16
    | exact resolve eq16 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq1066 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (M.op X0 (σ y))) (M.op X1 (σ x))) X1) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1008 eq16
    | exact resolve eq16 eq1008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1240 : ∀ X0 : G, x = (M.op (M.op x (M.op X0 (M.op x y))) x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq721 eq16
    | exact resolve eq16 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq1268 : ∀ X0 X1 : G, (M.op (M.op (M.op x (M.op X0 (M.op x y))) (M.op X1 x)) X1) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1240 eq16
    | exact resolve eq16 eq1240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240
  have eq2101 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op y (M.op X0 X1))) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq177 y X0 X1 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 y X0 X1 x
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3593 : ∀ X0 : G, (M.op (M.op X0 (σ x)) X0) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq592 eq1066
    | exact resolve eq1066 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592 eq1066
  have eq3653 : ∀ X0 : G, (M.op (M.op X0 (σ x)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq3593 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3593
  have eq3864 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3653 eq3653
    | exact resolve eq3653 eq3653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3653
  have eq3929 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by grind
  clear eq3864
  have eq3974 : (M.op (σ x) (σ x)) = (k (σ x) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3929
       have i₂ := eq179 sF2
       grind)
    | exact superpose eq179 eq3929
    | exact resolve eq3929 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3929
  have eq4101 : (τ (M.op (σ x) (σ x))) = (k x (τ (M.op (σ x) (σ x)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3974 eq91
    | exact resolve eq91 eq3974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq3974
  have eq4526 : (τ (M.op (σ x) (σ x))) ≠ (τ (M.op (σ x) (σ x))) ∨ (τ (M.op (σ x) (σ x))) = (M.op x (τ (M.op (σ x) (σ x)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4101 eq566
    | (have j0 := eq566 x (τ (M.op (σ x) (σ x)))
       grind)
    | (have r₁ := eq566 x (τ (M.op (σ x) (σ x)))
       have r₂ := eq4101
       grind)
    | exact resolve eq566 eq4101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4101
  have eq4527 : (τ (M.op (σ x) (σ x))) = (M.op x (τ (M.op (σ x) (σ x)))) ∨ y = (M.op x y) := by grind
  clear eq4526
  have eq4676 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq588 eq793
    | (have r₁ := eq793
       have r₂ := eq588
       grind)
    | exact resolve eq793 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588 eq793
  have eq4677 : (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq4676
  have eq4678 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq573 eq4677
    | exact resolve eq4677 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573 eq4677
  have eq4679 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq623 eq4678
    | exact resolve eq4678 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623 eq4678
  have eq4805 : (τ (σ y)) = (M.op x (τ (σ y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4679 eq4527
    | exact resolve eq4527 eq4679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4527 eq4679
  have eq4842 : (τ (σ y)) = (M.op x (τ (σ y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4805
  have eq4856 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq32 eq4842
    | exact resolve eq4842 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq4842
  have eq4862 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4856
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4856
    | exact resolve eq4856 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4856
  have eq4863 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq4862
  have eq4867 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4863 eq29
    | exact resolve eq29 eq4863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq4871 : (k y (M.op x y)) = (τ (k (σ y) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4863 eq117
    | exact resolve eq117 eq4863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq4863
  have eq4884 : (k y x) = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq115 eq4871
    | exact resolve eq4871 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq4871
  have eq4888 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq4867
    | exact resolve eq4867 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq4867
  have eq4892 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4888
       grind)
    | exact superpose eq4888 eq18
    | exact resolve eq18 eq4888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4893 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq4888
       grind)
    | exact superpose eq4888 eq24
    | exact resolve eq24 eq4888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4896 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (k x (M.op x y)) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq792
       have i₂ := eq4888
       grind)
    | exact superpose eq4888 eq792
    | (have r₁ := eq792
       have r₂ := eq4888
       grind)
    | exact resolve eq792 eq4888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq4897 : (k x (M.op x y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq4896
  have eq4900 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq4893
    | exact resolve eq4893 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4893
  have eq4955 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op (M.op x y) (M.op X0 X1))) (M.op x y)) x) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq4892 eq177
    | exact resolve eq177 eq4892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4960 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4955 x x
       have i₂ := eq16 sF0 x x
       grind)
    | exact superpose eq16 eq4955
    | exact resolve eq4955 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4955
  have eq4984 : x ≠ x ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (k (M.op x y) x) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4960 eq12
    | (have j0 := eq12 (M.op x y) x
       grind)
    | (have r₁ := eq12 (M.op x y) x
       have r₂ := eq4960
       grind)
    | exact resolve eq12 eq4960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4985 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op X0 x)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4960 eq16
    | exact resolve eq16 eq4960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4991 : x = (M.op (M.op x y) (M.op x y)) ∨ (k (M.op x y) x) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq4984
  have eq4993 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4892 eq4991
    | exact resolve eq4991 eq4892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4991
  have eq5013 : y = (k y (M.op x y)) ∨ x = (k y (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq859
       have i₂ := eq4884
       grind)
    | exact superpose eq4884 eq859
    | exact resolve eq859 eq4884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859 eq4884
  have eq5018 : y = (k y (M.op x y)) ∨ x = (k y (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq5013
  have eq5024 : (M.op x y) = (k y (M.op x y)) ∨ y = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4888 eq5018
    | exact resolve eq5018 eq4888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5018
  have eq5357 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X0 x)) = (M.op (M.op (M.op X1 (M.op X0 (M.op X1 X2))) X0) (M.op (M.op x y) (M.op X0 x))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq4985 eq177
    | exact resolve eq177 eq4985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5397 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 x)) = (M.op X0 (M.op (M.op x y) (M.op X0 x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq5357 X0 x x
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq5357
    | exact resolve eq5357 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5357
  have eq5511 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5024 eq566
    | (have j0 := eq566 y (M.op x y)
       grind)
    | (have r₁ := eq566 y (M.op x y)
       have r₂ := eq5024
       grind)
    | exact resolve eq566 eq5024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5024
  have eq5513 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (k y (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq5511
  have eq5584 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4993 eq40
    | exact resolve eq40 eq4993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq4993
  have eq5587 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq5584
    | exact resolve eq5584 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5584
  have eq5589 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4900 eq5587
    | exact resolve eq5587 eq4900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5587
  have eq5958 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5589 eq566
    | (have j0 := eq566 (σ y) (σ x)
       grind)
    | exact resolve eq566 eq5589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7271 : x = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4897 eq4960
    | exact resolve eq4960 eq4897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4897 eq4960
  have eq7286 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by grind
  clear eq7271
  have eq7295 : (k x (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq179 x
       have i₂ := eq7286
       grind)
    | exact superpose eq7286 eq179
    | exact resolve eq179 eq7286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7286
  have eq7309 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq4892 eq7295
    | exact resolve eq7295 eq4892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4892 eq7295
  have eq7992 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq7309 eq36
    | exact resolve eq36 eq7309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq7309
  have eq8001 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq20 eq7992
    | exact resolve eq7992 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7992
  have eq8003 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq4900 eq8001
    | exact resolve eq8001 eq4900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8001
  have eq8026 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq8003 eq548
    | exact resolve eq548 eq8003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8003
  have eq8035 : x = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8026
  have eq8051 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8035 eq42
    | exact resolve eq42 eq8035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq8035
  have eq8056 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8051
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8051
    | exact resolve eq8051 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8051
  have eq8058 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4900 eq8056
    | exact resolve eq8056 eq4900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8056
  have eq8066 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8058 eq548
    | exact resolve eq548 eq8058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548 eq8058
  have eq8076 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8066
  have eq8092 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8076 eq27
    | exact resolve eq27 eq8076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8076
  have eq8095 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8092
       have r₂ := eq4900
       grind)
    | exact resolve eq8092 eq4900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8092
  have eq8100 : ∀ X0 : G, (M.op (M.op (σ x) (M.op X0 (σ x))) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8095 eq176
    | exact resolve eq176 eq8095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq8101 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8095 eq27
    | exact resolve eq27 eq8095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8103 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4900 eq8101
    | exact resolve eq8101 eq4900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8101
  have eq8106 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq8103
  have eq8489 : ∀ X0 : G, (M.op (M.op (σ x) (k X0 (σ x))) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq8100 X0
       have i₂ := eq28 X0 sF2
       grind)
    | exact superpose eq28 eq8100
    | (have j1 := eq28 (M.op (σ x) (k X0 (σ x))) X0
       grind)
    | exact resolve eq8100 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8539 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (M.op (M.op X1 (M.op X0 (M.op X1 X2))) X0) (M.op (σ x) (M.op X0 (σ x)))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq8100 eq177
    | exact resolve eq177 eq8100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8594 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op X0 (M.op (σ x) (M.op X0 (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8539 X0 x x
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq8539
    | exact resolve eq8539 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8539
  have eq11613 : ∀ X0 : G, (M.op (M.op X0 x) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq175 eq1268
    | exact resolve eq1268 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268
  have eq11842 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4888 eq11613
    | exact resolve eq11613 eq4888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11613
  have eq12011 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op x y)) (M.op X1 X0)) X1) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq11842 eq16
    | exact resolve eq16 eq11842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12543 : x = (M.op (M.op (M.op y (M.op x y)) (M.op x y)) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12011 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12011
    | (have j0 := eq12011 y x
       grind)
    | exact resolve eq12011 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12011
  have eq12864 : (M.op x y) = (M.op (M.op (M.op y (M.op x y)) (M.op x y)) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4888 eq12543
    | exact resolve eq12543 eq4888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4888 eq12543
  have eq13039 : (M.op x y) = (M.op (M.op (k y (M.op x y)) (M.op x y)) (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq12864
       have i₂ := eq28 y sF0
       grind)
    | exact superpose eq28 eq12864
    | (have j1 := eq28 (M.op (k y (M.op x y)) (M.op x y)) (M.op x y)
       grind)
    | exact resolve eq12864 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12864
  have eq13100 : (M.op x y) = (M.op (M.op y (M.op x y)) (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq5513 eq13039
    | exact resolve eq13039 eq5513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13039
  have eq13102 : (M.op x y) = (M.op (k y (M.op x y)) (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq28 eq13100
    | (have j1 := eq28 (k y (M.op x y)) (M.op x y)
       grind)
    | exact resolve eq13100 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq13100
  have eq13103 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq5513 eq13102
    | exact resolve eq13102 eq5513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5513 eq13102
  have eq13104 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq13103
  have eq13116 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13104 eq11842
    | exact resolve eq11842 eq13104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11842 eq13104
  have eq13141 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) := by grind
  clear eq13116
  have eq67531 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) (M.op X0 x)) (M.op X1 (M.op x y))) X1) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq5397 eq177
    | exact resolve eq177 eq5397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5397
  have eq73726 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) X0) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4985 eq67531
    | exact resolve eq67531 eq4985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4985 eq67531
  have eq73916 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq73726 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73726
  have eq74182 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq73916 eq73916
    | exact resolve eq73916 eq73916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74201 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op x y)) (M.op X1 X0)) X1) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq73916 eq16
    | exact resolve eq16 eq73916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74390 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq74182
  have eq74428 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74390
       have i₂ := eq179 sF0
       grind)
    | exact superpose eq179 eq74390
    | exact resolve eq74390 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74390
  have eq74765 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq74428 eq38
    | exact resolve eq38 eq74428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq74428
  have eq74773 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ y) (σ (M.op (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4900 eq74765
    | exact resolve eq74765 eq4900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4900 eq74765
  have eq75713 : (σ (M.op (M.op x y) (M.op x y))) ≠ (σ (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ y) (σ (M.op (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq74773 eq566
    | (have j0 := eq566 (σ y) (σ (M.op (M.op x y) (M.op x y)))
       grind)
    | (have r₁ := eq566 (σ y) (σ (M.op (M.op x y) (M.op x y)))
       have r₂ := eq74773
       grind)
    | exact resolve eq566 eq74773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566 eq74773
  have eq75714 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ y) (σ (M.op (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by grind
  clear eq75713
  have eq75758 : (σ y) = (M.op (M.op (M.op (σ (M.op (M.op x y) (M.op x y))) (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq75714 eq74201
    | exact resolve eq74201 eq75714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74201 eq75714
  have eq75759 : (σ y) = (M.op (M.op (M.op (σ (M.op (M.op x y) (M.op x y))) (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq75758
  have eq75762 : (σ y) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq73916 eq75759
    | exact resolve eq75759 eq73916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73916 eq75759
  have eq96453 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (M.op X0 (σ x))) (M.op X1 (σ x))) X1) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq8594 eq177
    | exact resolve eq177 eq8594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq8594
  have eq102142 : ∀ X0 : G, (M.op (M.op X0 (σ x)) X0) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8100 eq96453
    | exact resolve eq96453 eq8100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8100 eq96453
  have eq102405 : ∀ X0 : G, (M.op (M.op X0 (σ x)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq102142 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102142
  have eq170142 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5589 eq8489
    | (have j0 := eq8489 (σ y)
       grind)
    | exact resolve eq8489 eq5589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5589 eq8489
  have eq170518 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq170142
  have eq170576 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26 eq170518
    | exact resolve eq170518 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170518
  have eq170587 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq8095 eq170576
    | exact resolve eq170576 eq8095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170576
  have eq170590 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26 eq170587
    | exact resolve eq170587 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170587
  have eq170591 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq8095 eq170590
    | exact resolve eq170590 eq8095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170590
  have eq170592 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq170591
       have r₂ := eq5958
       grind)
    | exact resolve eq170591 eq5958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5958 eq170591
  have eq170650 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq170592 eq102405
    | exact resolve eq102405 eq170592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102405 eq170592
  have eq170705 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq170650
  have eq170754 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26 eq170705
    | exact resolve eq170705 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170705
  have eq170790 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq8095 eq170754
    | exact resolve eq170754 eq8095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170754
  have eq170816 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq170790
       have r₂ := eq8106
       grind)
    | exact resolve eq170790 eq8106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170790
  have eq170884 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq170816 eq75762
    | exact resolve eq75762 eq170816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75762 eq170816
  have eq171002 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq170884
  have eq171038 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq171002
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq171002
    | exact resolve eq171002 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171002
  have eq171049 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq171038
    | exact resolve eq171038 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171038
  have eq171054 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8095 eq171049
    | exact resolve eq171049 eq8095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8095 eq171049
  have eq171055 : x = (M.op x y) := by
    first
    | (have r₁ := eq171054
       have r₂ := eq8106
       grind)
    | exact resolve eq171054 eq8106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8106 eq171054
  have eq171056 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq171055
       grind)
    | exact superpose eq171055 eq18
    | exact resolve eq18 eq171055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq171057 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq171055
       grind)
    | exact superpose eq171055 eq22
    | exact resolve eq22 eq171055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq171060 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op X0 (M.op x y))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq171055
       grind)
    | exact superpose eq171055 eq175
    | exact resolve eq175 eq171055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq171126 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq171057 eq20
    | exact resolve eq20 eq171057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171259 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq171056 eq13141
    | exact resolve eq13141 eq171056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13141
  have eq171298 : x = (M.op (M.op (M.op (M.op x y) (M.op y (M.op x y))) (M.op x y)) x) := by
    first
    | exact superpose eq171056 eq2101
    | exact resolve eq2101 eq171056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2101 eq171056
  have eq171316 : y = (M.op x y) := by grind
  clear eq171259
  have eq171320 : (M.op x y) = (M.op (M.op (M.op (M.op x y) (M.op y (M.op x y))) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq171298
       have i₂ := eq171055
       grind)
    | exact superpose eq171055 eq171298
    | exact resolve eq171298 eq171055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171055 eq171298
  have eq171330 : (M.op x y) = (M.op (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq171320
       have i₂ := eq171316
       grind)
    | exact superpose eq171316 eq171320
    | exact resolve eq171320 eq171316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171320
  have eq171335 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq171060 eq171330
    | exact resolve eq171330 eq171060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171060 eq171330
  have eq171340 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq171316
       grind)
    | exact superpose eq171316 eq24
    | exact resolve eq24 eq171316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq171316
  have eq171351 : (σ x) = (σ y) := by
    first
    | exact superpose eq171057 eq171340
    | exact resolve eq171340 eq171057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171057 eq171340
  have eq171354 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq171351 eq26
    | exact resolve eq26 eq171351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq171351
  have eq171721 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq171335 eq179
    | exact resolve eq179 eq171335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq171770 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq171335 eq171721
    | exact resolve eq171721 eq171335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171335 eq171721
  have eq171812 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq171770 eq817
    | (have j0 := eq817 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq817 eq171770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817 eq171770
  have eq171819 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq171812
  have eq171826 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq171819
    | exact resolve eq171819 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq171819
  have eq171829 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq171126 eq171826
    | exact resolve eq171826 eq171126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171826
  have eq172051 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq171829 eq171354
    | exact resolve eq171354 eq171829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171354 eq171829
  have eq172167 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq172051 eq27
    | exact resolve eq27 eq172051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq172051
  have eq172184 : False := by grind
  exact eq172184

/-- `Equation2306`: `x = (y ◇ (x ◇ (y ◇ z))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_pxy_x_pxy_Equation2306 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2306 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2306.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X2))) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op (M.op x (M.op X0 (M.op x y))) X0) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X0 (M.op X1 X2))) (M.op X3 X0)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op X1 (M.op X0 (M.op X1 X2))) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) (M.op X2 X3))) = (M.op (M.op X0 (M.op X0 X1)) (M.op X2 (M.op (M.op X0 X1) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op (M.op X0 X1) (M.op X2 X3))) X0 X1
       have i₂ := eq14 (M.op X0 X1) X2 X3
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
  have eq63 : x ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
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
  have eq64 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (k x y) := by
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
  have eq68 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
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
  have eq78 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq84 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq78 eq16
    | exact resolve eq16 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq84 x y
       grind)
    | exact superpose eq84 eq44
    | (have j1 := eq84 x y
       grind)
    | exact resolve eq44 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq104
    | exact resolve eq104 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq122 : (τ (σ (M.op x y))) = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq116 eq57
    | exact resolve eq57 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq116 eq84
    | (have j0 := eq84 (σ x) (σ y)
       grind)
    | exact resolve eq84 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq123
    | exact resolve eq123 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq125 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq122
    | exact resolve eq122 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq127 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq124
       have r₂ := eq27
       grind)
    | exact resolve eq124 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq129 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq127
    | exact resolve eq127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq143 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq129 eq64
    | exact resolve eq64 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq144 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq129 eq27
    | exact resolve eq27 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 X1 : G, (M.op (M.op (M.op x (M.op X0 (M.op x y))) (M.op X1 X0)) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 : G, (M.op (M.op (σ x) (M.op X0 (σ y))) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq129 eq51
    | exact resolve eq51 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq228
    | (have j0 := eq228 (σ x)
       grind)
    | exact resolve eq228 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq255 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq129 eq238
    | exact resolve eq238 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq260 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq255
  have eq261 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq260
    | exact resolve eq260 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq285 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq129 eq261
    | exact resolve eq261 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq290 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq285
  have eq291 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq290 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq290
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq290
       grind)
    | exact resolve eq12 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq294 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq291
  have eq336 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq129 eq68
    | (have r₁ := eq68
       have r₂ := eq129
       grind)
    | exact resolve eq68 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq129
  have eq337 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq336
  have eq340 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq337 eq116
    | exact resolve eq116 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq341 : (τ (σ x)) = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq337 eq57
    | exact resolve eq57 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq337
  have eq343 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq340
  have eq346 : x = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq341
    | exact resolve eq341 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq351 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq343 eq29
    | exact resolve eq29 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq343 eq116
    | exact resolve eq116 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq359 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq343 eq143
    | (have r₁ := eq143
       have r₂ := eq343
       grind)
    | exact resolve eq143 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq343
  have eq370 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq359
  have eq371 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq370
  have eq372 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq358
  have eq380 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq351
    | exact resolve eq351 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq381 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 (M.op X0 (M.op X1 X2))) (M.op X3 X0)) (M.op X4 X3)) X4) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X3 (M.op X1 (M.op X0 (M.op X1 X2))) X0 X4
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq397 : ∀ X0 X1 X2 : G, (M.op x (M.op X0 (M.op x y))) = (M.op (M.op (M.op X1 (M.op X0 (M.op X1 X2))) X0) (M.op x (M.op X0 (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq402 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op y (M.op X0 X1))) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq52 y X0 X1 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 y X0 X1 x
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq421 : ∀ X0 : G, (M.op x (M.op X0 (M.op x y))) = (M.op X0 (M.op x (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq397 X0 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq397
    | exact resolve eq397 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq438 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq380 eq28
    | exact resolve eq28 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq380
  have eq475 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq438
    | exact resolve eq438 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq438
  have eq480 : y ≠ y ∨ x = y ∨ x = (k x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq475 eq67
    | (have r₁ := eq67
       have r₂ := eq475
       grind)
    | exact resolve eq67 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq486 : y ≠ y ∨ x = y ∨ x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq480
  have eq487 : x = y ∨ x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq486
  have eq566 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq125
       have i₂ := eq346
       grind)
    | exact superpose eq346 eq125
    | exact resolve eq125 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq346
  have eq569 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq566
  have eq589 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq569 eq144
    | exact resolve eq144 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq600 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq589
  have eq687 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op (M.op X4 (M.op (M.op X0 (M.op (M.op X1 X2) (M.op X0 X3))) (M.op X4 X5))) (M.op X0 (M.op (M.op X1 X2) (M.op X0 X3)))) (M.op X1 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X3))) X4 X5 (M.op X1 (M.op X1 X2))
       have i₂ := eq53 X1 X2 X0 X3
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq690 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X0 (M.op (M.op X1 X2) (M.op X0 X3))) (M.op X1 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq687 X0 X1 X2 X3 x x
       have i₂ := eq14 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X3))) x x
       grind)
    | exact superpose eq14 eq687
    | exact resolve eq687 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq698 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq372 eq371
    | exact resolve eq371 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371 eq372
  have eq701 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq698
  have eq720 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq701 eq294
    | exact resolve eq294 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq723 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq701 eq600
    | (have r₁ := eq600
       have r₂ := eq701
       grind)
    | exact resolve eq600 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600 eq701
  have eq724 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq723
  have eq725 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq724
  have eq728 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq720
  have eq736 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq728
       have r₂ := eq144
       grind)
    | exact resolve eq728 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq728
  have eq769 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq725 eq20
    | exact resolve eq20 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq778 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq725
  have eq785 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq769
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq769
    | exact resolve eq769 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq910 : (τ (σ y)) = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq736 eq94
    | exact resolve eq94 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq736
  have eq914 : y = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq910
    | exact resolve eq910 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq910
  have eq989 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq914
       have i₂ := eq84 y sF0
       grind)
    | exact superpose eq84 eq914
    | (have j1 := eq84 y (M.op x y)
       grind)
    | exact resolve eq914 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914
  have eq1356 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op y (M.op X0 X1))) y) x) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq475 eq402
    | exact resolve eq402 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq1373 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op y (M.op X0 X1))) y) x) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq1356 X0 X1
       grind)
    | (have r₁ := eq1356 X0 X1
       have r₂ := eq778
       grind)
    | exact resolve eq1356 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1356
  have eq1375 : x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1373 x x
       have i₂ := eq14 y x x
       grind)
    | exact superpose eq14 eq1373
    | exact resolve eq1373 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1373
  have eq1376 : x ≠ x ∨ x = y ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1375
       grind)
    | exact superpose eq1375 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1375
       grind)
    | exact resolve eq12 eq1375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375
  have eq1388 : x = y ∨ y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq1376
  have eq1392 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1388
       have r₂ := eq778
       grind)
    | exact resolve eq1388 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1388
  have eq1397 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq1392
       grind)
    | exact superpose eq1392 eq76
    | exact resolve eq76 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq1392
  have eq1399 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1397
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1397
    | exact resolve eq1397 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397
  have eq1460 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1399
       have i₂ := eq84 sF3 sF2
       grind)
    | exact superpose eq84 eq1399
    | (have j1 := eq84 (σ y) (σ x)
       grind)
    | exact resolve eq1399 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399
  have eq1568 : x = (M.op (M.op (M.op x (M.op x (M.op y (M.op x y)))) (M.op x y)) x) := by
    first
    | exact superpose eq421 eq402
    | exact resolve eq402 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402 eq421
  have eq2633 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq487
       have r₂ := eq778
       grind)
    | exact resolve eq487 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487 eq778
  have eq2637 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq2633
       grind)
    | exact superpose eq2633 eq44
    | exact resolve eq44 eq2633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2633
  have eq2643 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2637
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2637
    | exact resolve eq2637 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2637
  have eq2662 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2643 eq84
    | (have j0 := eq84 (σ x) (σ y)
       grind)
    | exact resolve eq84 eq2643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2643
  have eq2668 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2662
    | exact resolve eq2662 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2662
  have eq2672 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2668
    | exact resolve eq2668 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2668
  have eq2799 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2672 eq27
    | exact resolve eq27 eq2672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2672
  have eq2827 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2799
       have r₂ := eq785
       grind)
    | exact resolve eq2799 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2799
  have eq2902 : ∀ X0 : G, (M.op (M.op (σ x) (M.op X0 (σ x))) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2827 eq51
    | exact resolve eq51 eq2827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq10565 : ∀ X0 X1 X4 : G, (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op X4 X0)) X4) = X4 := by
    intro X0 X1 X4
    first
    | (have i₁ := eq381 (M.op X0 X1) x x X0 X4
       have i₂ := eq690 x X0 X1 x
       grind)
    | exact superpose eq690 eq381
    | exact resolve eq381 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq10566 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X0 X1) x x X0
       have i₂ := eq690 x X0 X1 x
       grind)
    | exact superpose eq690 eq52
    | exact resolve eq52 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq690
  have eq90256 : ∀ X0 : G, y = (M.op (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op x y)) y) ∨ y = (M.op x y) ∨ y = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq989 eq10565
    | exact resolve eq10565 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq90261 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq90256 x
       have i₂ := eq10566 sF0 x
       grind)
    | exact superpose eq10566 eq90256
    | exact resolve eq90256 eq10566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90256
  have eq90307 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1460 eq2902
    | exact resolve eq2902 eq1460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1460 eq2902
  have eq90421 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq90307
  have eq90429 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq90421
    | exact resolve eq90421 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90421
  have eq99215 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2827 eq90429
    | exact resolve eq90429 eq2827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2827 eq90429
  have eq99341 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq99215
  have eq99373 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq99341
    | exact resolve eq99341 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99341
  have eq99510 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (M.op (σ x) X0)) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq99373 eq10565
    | exact resolve eq10565 eq99373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10565 eq99373
  have eq99520 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq99510 x
       have i₂ := eq10566 sF2 x
       grind)
    | exact superpose eq10566 eq99510
    | exact resolve eq99510 eq10566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99510
  have eq99553 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq99520
    | exact resolve eq99520 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99520
  have eq99554 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq99553
  have eq99577 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq99554 eq27
    | exact resolve eq27 eq99554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99554
  have eq99891 : x = (M.op x y) := by
    first
    | (have r₁ := eq99577
       have r₂ := eq785
       grind)
    | exact resolve eq99577 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785 eq99577
  have eq100137 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq99891 eq20
    | exact resolve eq20 eq99891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq100141 : x ≠ x ∨ x = (k x y) := by
    first
    | exact superpose eq99891 eq63
    | (have r₁ := eq63
       have r₂ := eq99891
       grind)
    | exact resolve eq63 eq99891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq100238 : x = (M.op (M.op (M.op x (M.op x (M.op y x))) x) x) := by
    first
    | exact superpose eq99891 eq1568
    | exact resolve eq1568 eq99891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1568
  have eq100262 : y = (M.op x y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq99891 eq90261
    | exact resolve eq90261 eq99891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90261
  have eq100264 : x = (k x y) := by grind
  clear eq100141
  have eq100266 : y = (M.op x y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq100262
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100262
    | exact resolve eq100262 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100262
  have eq100267 : x = (M.op x x) := by
    first
    | (have i₁ := eq100238
       have i₂ := eq10566 x (M.op y x)
       grind)
    | exact superpose eq10566 eq100238
    | exact resolve eq100238 eq10566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10566 eq100238
  have eq100330 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq100137
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq100137
    | exact resolve eq100137 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100137
  have eq100331 : x = y ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq99891 eq100266
    | exact resolve eq100266 eq99891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100266
  have eq100332 : y = (M.op y x) ∨ x = y := by grind
  clear eq100331
  have eq100335 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq100330 eq26
    | exact resolve eq26 eq100330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq101049 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq100264
       grind)
    | exact superpose eq100264 eq44
    | exact resolve eq44 eq100264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq100264
  have eq101094 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq100330 eq101049
    | exact resolve eq101049 eq100330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101049
  have eq101115 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq101094
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq101094
    | exact resolve eq101094 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101094
  have eq101133 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq100330 eq101115
    | exact resolve eq101115 eq100330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101115
  have eq101587 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq101133 eq84
    | (have j0 := eq84 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq84 eq101133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq101133
  have eq101598 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq100335 eq101587
    | exact resolve eq101587 eq100335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101587
  have eq101606 : (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq101598
       have r₂ := eq27
       grind)
    | exact resolve eq101598 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101598
  have eq101611 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq100335 eq101606
    | exact resolve eq101606 eq100335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100335 eq101606
  have eq101617 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq101611 eq27
    | exact resolve eq27 eq101611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq101611
  have eq108567 : y = (M.op (M.op (M.op x (M.op x (M.op x y))) y) y) ∨ x = y := by
    first
    | (have i₁ := eq225 x y
       have i₂ := eq100332
       grind)
    | exact superpose eq100332 eq225
    | exact resolve eq225 eq100332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225 eq100332
  have eq108697 : y = (M.op (M.op (M.op x (M.op x x)) y) y) ∨ x = y := by
    first
    | exact superpose eq99891 eq108567
    | exact resolve eq108567 eq99891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108567
  have eq108723 : y = (M.op (M.op (M.op x x) y) y) ∨ x = y := by
    first
    | (have i₁ := eq108697
       have i₂ := eq100267
       grind)
    | exact superpose eq100267 eq108697
    | exact resolve eq108697 eq100267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108697
  have eq108736 : y = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq108723
       have i₂ := eq100267
       grind)
    | exact superpose eq100267 eq108723
    | exact resolve eq108723 eq100267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100267 eq108723
  have eq108745 : y = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq108736
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq108736
    | exact resolve eq108736 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108736
  have eq108750 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq99891 eq108745
    | exact resolve eq108745 eq99891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108745
  have eq108751 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq108750
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq108750
    | exact resolve eq108750 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq108750
  have eq108752 : x = y ∨ x = y := by
    first
    | exact superpose eq99891 eq108751
    | exact resolve eq108751 eq99891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99891 eq108751
  have eq108753 : x = y := by grind
  clear eq108752
  have eq108755 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq108753
       grind)
    | exact superpose eq108753 eq24
    | exact resolve eq24 eq108753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq108753
  have eq108975 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq108755
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq108755
    | exact resolve eq108755 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq108755
  have eq109044 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq100330 eq108975
    | exact resolve eq108975 eq100330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100330 eq108975
  have eq109100 : False := by grind
  exact eq109100

/-- `Equation2310`: `x = (y ◇ (x ◇ (z ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_y_pyx_Equation2310 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2310 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2310.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) = X0 := by
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op x (M.op X0 (M.op x X0)))
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op x (M.op (M.op X0 (M.op X1 X0)) (M.op x (M.op X0 (M.op X1 X0))))) X1
       have i₂ := eq14 (M.op X0 (M.op X1 X0)) x x
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
  clear eq36
  have eq75 : x ≠ (M.op x y) ∨ y = (M.op y x) ∨ y = (k x y) := by
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
  have eq76 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
  have eq132 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq621 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq93 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq93 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq12 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq622 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq626 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq93 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq627 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq628 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq626 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq631 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq621 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq632 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq622 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq622 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq622 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq622 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq633 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq631 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq631 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq631 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq631 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq642 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq632 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq632
    | (have j0 := eq632 X0 X1
       grind)
    | exact resolve eq632 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq643 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq633 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq633
    | (have j0 := eq633 X0 X1
       grind)
    | exact resolve eq633 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq2934 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq628 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq628
    | (have j0 := eq628 (τ X0)
       grind)
    | exact resolve eq628 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq628
  have eq2942 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2934 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2934
    | (have j0 := eq2934 X0
       grind)
    | exact resolve eq2934 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2934
  have eq2948 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2942 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2942
    | (have j0 := eq2942 X0
       grind)
    | exact resolve eq2942 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2942
  have eq3175 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq3186 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3175
  have eq3191 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3186
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq3186
    | exact resolve eq3186 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq3186
  have eq3209 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq3191
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq3191 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3191
  have eq3214 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq3209 eq49
    | exact resolve eq49 eq3209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq3209
  have eq13935 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13943 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq13935
    | exact resolve eq13935 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13935
  have eq13954 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq13943
       have r₂ := eq27
       grind)
    | exact resolve eq13943 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13943
  have eq13956 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq13954
    | exact resolve eq13954 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13954
  have eq13958 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq13956 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq13956
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq13956
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq13956
       grind)
    | exact resolve eq12 eq13956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13956
  have eq13967 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq13958
  have eq13975 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq13967
    | exact resolve eq13967 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13967
  have eq13976 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq13975
  have eq14144 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq13976 eq82
    | exact resolve eq82 eq13976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14145 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq13976 eq115
    | exact resolve eq115 eq13976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13976
  have eq14164 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14145
  have eq14173 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq28 eq14144
    | exact resolve eq14144 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14144
  have eq14176 : y ≠ y ∨ x = (M.op x y) ∨ x = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq14164
       grind)
    | exact superpose eq14164 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq14164
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq14164
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq14164
       grind)
    | exact resolve eq12 eq14164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14177 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq14164
       grind)
    | exact superpose eq14164 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq14164
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq14164
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq14164
       grind)
    | exact resolve eq13 eq14164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14164
  have eq14184 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14177
  have eq14185 : x = (M.op x y) ∨ x = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14176
  have eq14192 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14184
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14184
    | exact resolve eq14184 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14184
  have eq14193 : x = (M.op x y) ∨ x = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14185
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14185
    | exact resolve eq14185 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14185
  have eq14194 : x = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14193
  have eq14342 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq14192
       grind)
    | exact superpose eq14192 eq44
    | exact resolve eq44 eq14192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14192
  have eq14370 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq14342
    | exact resolve eq14342 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14342
  have eq14576 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq627 x y
       have i₂ := eq14194
       grind)
    | exact superpose eq14194 eq627
    | (have j0 := eq627 x y
       grind)
    | exact resolve eq627 eq14194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14194
  have eq14583 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14576
  have eq14590 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14583
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14583
    | exact resolve eq14583 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14583
  have eq14604 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14590
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14590
    | exact resolve eq14590 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14590
  have eq14613 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14604
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14604
    | exact resolve eq14604 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14604
  have eq14620 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14613
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14613
    | exact resolve eq14613 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14613
  have eq14626 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq14620
    | exact resolve eq14620 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14620
  have eq14627 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq14626
  have eq14859 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq14627 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq14627
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq14627
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq14627
       grind)
    | exact resolve eq13 eq14627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14627
  have eq14866 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq14859
  have eq14874 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq14866
    | exact resolve eq14866 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14866
  have eq14898 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq14874 eq14370
    | exact resolve eq14370 eq14874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14370 eq14874
  have eq14907 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14898
  have eq14909 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14907
       have r₂ := eq27
       grind)
    | exact resolve eq14907 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14907
  have eq14914 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14909 eq64
    | (have r₁ := eq64
       have r₂ := eq14909
       grind)
    | exact resolve eq64 eq14909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14920 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq14914
  have eq14940 : (k y x) = (τ (M.op (σ y) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14920 eq82
    | exact resolve eq82 eq14920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq14920
  have eq15021 : y ≠ y ∨ x = (M.op x y) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq14173
       grind)
    | exact superpose eq14173 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq14173
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq14173
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq14173
       grind)
    | exact resolve eq12 eq14173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14173
  have eq15030 : y ≠ y ∨ x = (M.op x y) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15021
  have eq15031 : x = (M.op x y) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15030
  have eq15039 : x = (M.op x y) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15031
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15031
    | exact resolve eq15031 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15031
  have eq15040 : x = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15039
  have eq15052 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq15040
       grind)
    | exact superpose eq15040 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq15040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15055 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq627 x y
       have i₂ := eq15040
       grind)
    | exact superpose eq15040 eq627
    | (have j0 := eq627 x y
       grind)
    | exact resolve eq627 eq15040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15057 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq643 y x
       have i₂ := eq15040
       grind)
    | exact superpose eq15040 eq643
    | (have j0 := eq643 y x
       grind)
    | exact resolve eq643 eq15040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643 eq15040
  have eq15060 : (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15057
  have eq15062 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15055
  have eq15063 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15052
  have eq15067 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15060
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq15060
    | exact resolve eq15060 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15060
  have eq15069 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15062
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15062
    | exact resolve eq15062 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15062
  have eq15072 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15063
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15063
    | exact resolve eq15063 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15063
  have eq15073 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15072
  have eq15085 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15067
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15067
    | exact resolve eq15067 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15067
  have eq15087 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15069
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15069
    | exact resolve eq15069 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15069
  have eq15094 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15085
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15085
    | exact resolve eq15085 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15085
  have eq15096 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15087
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15087
    | exact resolve eq15087 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15087
  have eq15101 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15094
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15094
    | exact resolve eq15094 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15094
  have eq15103 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15096
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15096
    | exact resolve eq15096 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15096
  have eq15108 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15101
       have r₂ := eq76
       grind)
    | exact resolve eq15101 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq15101
  have eq15109 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq15103
    | exact resolve eq15103 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15103
  have eq15110 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15109
  have eq15133 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq15073
       grind)
    | exact superpose eq15073 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq15073
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq15073
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq15073
       grind)
    | exact resolve eq13 eq15073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15073
  have eq15140 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15133
  have eq15148 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15140
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15140
    | exact resolve eq15140 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15140
  have eq15201 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15110 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq15110
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq15110
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq15110
       grind)
    | exact resolve eq13 eq15110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15110
  have eq15208 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15201
  have eq15219 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq15208
    | exact resolve eq15208 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15208
  have eq15232 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq15148
       grind)
    | exact superpose eq15148 eq44
    | exact resolve eq44 eq15148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15148
  have eq15260 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq15232
    | exact resolve eq15232 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15232
  have eq15364 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15260 eq15219
    | exact resolve eq15219 eq15260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15219 eq15260
  have eq15373 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15364
  have eq15379 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15373
       have r₂ := eq27
       grind)
    | exact resolve eq15373 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15373
  have eq15391 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15379 eq27
    | exact resolve eq27 eq15379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15393 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15379 eq64
    | (have r₁ := eq64
       have r₂ := eq15379
       grind)
    | exact resolve eq64 eq15379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq15379
  have eq15399 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq15393
  have eq15424 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15399 eq115
    | exact resolve eq115 eq15399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq15445 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq15424
  have eq15523 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15108 eq57
    | exact resolve eq57 eq15108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq15108
  have eq15566 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq15523
    | exact resolve eq15523 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15523
  have eq15573 : (τ (σ y)) = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15566 eq14940
    | exact resolve eq14940 eq15566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14940
  have eq15578 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15566 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq15566
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq15566
       grind)
    | exact resolve eq13 eq15566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15580 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15566 eq53
    | exact resolve eq53 eq15566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15585 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (k x y) ∨ x = (M.op x y) := by grind
  clear eq15578
  have eq15590 : (τ (σ y)) = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (k x y) := by grind
  clear eq15573
  have eq15597 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq15580
    | exact resolve eq15580 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15580
  have eq15599 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq15585
    | exact resolve eq15585 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15585
  have eq15602 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | (have r₁ := eq15590
       have r₂ := eq15391
       grind)
    | exact resolve eq15590 eq15391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15590
  have eq15609 : y = (k y x) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq29 eq15602
    | exact resolve eq15602 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15602
  have eq15616 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14909 eq15597
    | exact resolve eq15597 eq14909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14909 eq15597
  have eq15625 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq15616
  have eq15629 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15625
       have r₂ := eq15391
       grind)
    | exact resolve eq15625 eq15391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15625
  have eq15662 : (τ (σ x)) = (k x x) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15629 eq3214
    | exact resolve eq3214 eq15629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3214 eq15629
  have eq15690 : y = (k x y) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq15662
    | exact resolve eq15662 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq15662
  have eq15734 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq15690
       grind)
    | exact superpose eq15690 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq15690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15690
  have eq15745 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x y) := by grind
  clear eq15734
  have eq15758 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15745
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15745
    | exact resolve eq15745 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15745
  have eq15759 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x x) := by grind
  clear eq15758
  have eq15826 : (σ (M.op x y)) = (σ y) ∨ y = (k x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq15445 eq15566
    | exact resolve eq15566 eq15445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15835 : (σ (M.op x y)) = (σ y) ∨ y = (k x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq15826
  have eq15851 : y = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq15835
       have r₂ := eq75
       grind)
    | exact resolve eq15835 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15835
  have eq15863 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq15609
       grind)
    | exact superpose eq15609 eq72
    | exact resolve eq72 eq15609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15609
  have eq15896 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq15863
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15863
    | exact resolve eq15863 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15863
  have eq15971 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq53 x y
       have i₂ := eq15759
       grind)
    | exact superpose eq15759 eq53
    | exact resolve eq53 eq15759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15982 : x = (k x x) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq15971
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15971
    | exact resolve eq15971 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15971
  have eq16072 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq15851
       grind)
    | exact superpose eq15851 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq15851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15851
  have eq16083 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq16072
  have eq16092 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq16083
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16083
    | exact resolve eq16083 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16083
  have eq16156 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq16092
       grind)
    | exact superpose eq16092 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq16092
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq16092
       grind)
    | exact resolve eq13 eq16092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16092
  have eq16163 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq16156
  have eq16171 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq16163
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16163
    | exact resolve eq16163 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16163
  have eq16189 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq16171
       grind)
    | exact superpose eq16171 eq44
    | exact resolve eq44 eq16171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16223 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq16189
    | exact resolve eq16189 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16189
  have eq16342 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq16223 eq15599
    | exact resolve eq15599 eq16223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15599 eq16223
  have eq16353 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq16342
  have eq16365 : y = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq16353
       have r₂ := eq27
       grind)
    | exact resolve eq16353 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16353
  have eq16540 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq16171
       have i₂ := eq16365
       grind)
    | exact superpose eq16365 eq16171
    | exact resolve eq16171 eq16365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16171 eq16365
  have eq16553 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq16540
  have eq16784 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16553 eq29
    | exact resolve eq29 eq16553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq16553
  have eq16967 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq16784
    | exact resolve eq16784 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq16784
  have eq16968 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq16967
  have eq16981 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16968 eq20
    | exact resolve eq20 eq16968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16998 : (σ (k y x)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16968 eq132
    | exact resolve eq132 eq16968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq17041 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq17078 : (k (σ y) (σ x)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16998
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16998
    | exact resolve eq16998 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16998
  have eq17094 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16981
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16981
    | exact resolve eq16981 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16981
  have eq17683 : (M.op (σ y) (σ x)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17078 eq15399
    | exact resolve eq15399 eq17078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15399 eq17078
  have eq17694 : (M.op (σ y) (σ x)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq17683
  have eq33361 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17094 eq15896
    | exact resolve eq15896 eq17094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15896 eq17094
  have eq33428 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ y = (k x y) := by grind
  clear eq33361
  have eq34438 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq15982
       grind)
    | exact superpose eq15982 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq15982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15982
  have eq34453 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq34438
  have eq34899 : x = (M.op y x) ∨ x = y ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16968 eq34453
    | exact resolve eq34453 eq16968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16968 eq34453
  have eq34908 : x = (M.op y x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq34899
       have r₂ := eq17041
       grind)
    | exact resolve eq34899 eq17041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34899
  have eq35804 : x = y ∨ x = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15759
       have i₂ := eq34908
       grind)
    | exact superpose eq34908 eq15759
    | exact resolve eq15759 eq34908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15759 eq34908
  have eq35817 : x = y ∨ x = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x x) := by grind
  clear eq35804
  have eq35827 : x = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq35817
       have r₂ := eq17041
       grind)
    | exact resolve eq35817 eq17041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35817
  have eq35835 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq2948 x
       grind)
    | (have r₁ := eq35827
       have r₂ := eq2948 x
       grind)
    | exact resolve eq35827 eq2948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2948 eq35827
  have eq35845 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq52 x X0
       have i₂ := eq35835
       grind)
    | exact superpose eq35835 eq52
    | exact resolve eq52 eq35835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35846 : x ≠ x ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq35835
       grind)
    | exact superpose eq35835 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq35835
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq35835
       grind)
    | exact resolve eq13 eq35835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35835
  have eq35853 : x = (k x x) ∨ x = (M.op x y) := by grind
  clear eq35846
  have eq35875 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq642 x x
       have i₂ := eq35853
       grind)
    | exact superpose eq35853 eq642
    | (have j0 := eq642 x x
       grind)
    | exact resolve eq642 eq35853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35853
  have eq35880 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq35875
  have eq35881 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq35880
  have eq35890 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35881
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35881
    | exact resolve eq35881 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35881
  have eq35931 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq35890 eq52
    | exact resolve eq52 eq35890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq35890
  have eq36104 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15566 eq35931
    | exact resolve eq35931 eq15566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15566 eq35931
  have eq36129 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (k x y) := by grind
  clear eq36104
  have eq38463 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq33428 eq17694
    | exact resolve eq17694 eq33428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17694 eq33428
  have eq38483 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (k x y) := by grind
  clear eq38463
  have eq74127 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq36129 eq15445
    | exact resolve eq15445 eq36129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15445
  have eq74134 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (k x y) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq36129 eq38483
    | exact resolve eq38483 eq36129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36129 eq38483
  have eq74149 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (k x y) := by grind
  clear eq74134
  have eq74156 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (k x y) := by grind
  clear eq74127
  have eq74182 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq74149
       have r₂ := eq15391
       grind)
    | exact resolve eq74149 eq15391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74149
  have eq74184 : x = (M.op x y) ∨ y = (M.op y x) ∨ y = (k x y) := by
    first
    | (have r₁ := eq74156
       have r₂ := eq15391
       grind)
    | exact resolve eq74156 eq15391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15391 eq74156
  have eq74194 : y = (k x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq74184
       have r₂ := eq75
       grind)
    | exact resolve eq74184 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq74184
  have eq74220 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq74182
       grind)
    | exact superpose eq74182 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq74182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74182
  have eq74231 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq74220
  have eq74250 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74231
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq74231
    | exact resolve eq74231 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74231
  have eq74251 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq74250
  have eq74310 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35845 y
       have i₂ := eq74251
       grind)
    | exact superpose eq74251 eq35845
    | exact resolve eq35845 eq74251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35845
  have eq74323 : x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq74310
  have eq74471 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74251
       have i₂ := eq74323
       grind)
    | exact superpose eq74323 eq74251
    | exact resolve eq74251 eq74323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74251 eq74323
  have eq74484 : x = y ∨ x = (M.op x y) := by grind
  clear eq74471
  have eq74498 : x = (M.op x y) := by
    first
    | (have r₁ := eq74484
       have r₂ := eq17041
       grind)
    | exact resolve eq74484 eq17041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17041 eq74484
  have eq74510 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq74498 eq20
    | exact resolve eq20 eq74498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq74514 : x ≠ x ∨ (k y x) = (M.op y x) := by
    first
    | exact superpose eq74498 eq63
    | (have r₁ := eq63
       have r₂ := eq74498
       grind)
    | exact resolve eq63 eq74498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq74634 : (k y x) = (M.op y x) := by grind
  clear eq74514
  have eq74741 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq74510
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq74510
    | exact resolve eq74510 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74510
  have eq74781 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq74741 eq26
    | exact resolve eq26 eq74741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75120 : (k (σ y) (σ x)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq74634
       grind)
    | exact superpose eq74634 eq72
    | exact resolve eq72 eq74634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq74634
  have eq75170 : (k (σ y) (σ (M.op x y))) = (σ (M.op y x)) := by
    first
    | exact superpose eq74741 eq75120
    | exact resolve eq75120 eq74741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75120
  have eq75437 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq627 y x
       have i₂ := eq74194
       grind)
    | exact superpose eq74194 eq627
    | (have j0 := eq627 y x
       grind)
    | exact resolve eq627 eq74194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq75438 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq642 x y
       have i₂ := eq74194
       grind)
    | exact superpose eq74194 eq642
    | (have j0 := eq642 x y
       grind)
    | exact resolve eq642 eq74194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642 eq74194
  have eq75443 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq75438
  have eq75444 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq75437
  have eq75450 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq75443
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq75443
    | exact resolve eq75443 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75443
  have eq75451 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq75444
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq75444
    | exact resolve eq75444 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75444
  have eq75470 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq75450
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq75450
    | exact resolve eq75450 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75450
  have eq75471 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq75451
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq75451
    | exact resolve eq75451 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75451
  have eq75488 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq75470
    | exact resolve eq75470 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75470
  have eq75489 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq75471
    | exact resolve eq75471 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75471
  have eq75499 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq75488
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq75488
    | exact resolve eq75488 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75488
  have eq75500 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq74741 eq75489
    | exact resolve eq75489 eq74741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75489
  have eq75506 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq75499
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq75499
    | exact resolve eq75499 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75499
  have eq75507 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq75500
       have r₂ := eq27
       grind)
    | exact resolve eq75500 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75500
  have eq75513 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq75506
    | exact resolve eq75506 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq75506
  have eq75514 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq75507
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq75507
    | exact resolve eq75507 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75507
  have eq75520 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq74741 eq75513
    | exact resolve eq75513 eq74741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75513
  have eq75521 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq74741 eq75514
    | exact resolve eq75514 eq74741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75514
  have eq75527 : y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq75520
       have r₂ := eq27
       grind)
    | exact resolve eq75520 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75520
  have eq75528 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq75521
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq75521
    | exact resolve eq75521 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75521
  have eq75566 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq75170
       have i₂ := eq75527
       grind)
    | exact superpose eq75527 eq75170
    | exact resolve eq75170 eq75527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75170
  have eq75570 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq75527
       grind)
    | exact superpose eq75527 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq75527
       grind)
    | exact resolve eq13 eq75527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75527
  have eq75577 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq75570
  have eq75586 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq75577
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq75577
    | exact resolve eq75577 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75577
  have eq75588 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq75566
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq75566
    | exact resolve eq75566 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75566
  have eq75595 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq74498 eq75586
    | exact resolve eq75586 eq74498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75586
  have eq75650 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq75595
       grind)
    | exact superpose eq75595 eq44
    | exact resolve eq44 eq75595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq75595
  have eq75705 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq74741 eq75650
    | exact resolve eq75650 eq74741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75650
  have eq75719 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq75705
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq75705
    | exact resolve eq75705 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75705
  have eq75732 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq74741 eq75719
    | exact resolve eq75719 eq74741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75719
  have eq76051 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq75588 eq11
    | (have j0 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq75588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75588
  have eq76063 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq74781 eq76051
    | exact resolve eq76051 eq74781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76051
  have eq76064 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq76063
  have eq76076 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq74781 eq76064
    | exact resolve eq76064 eq74781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76064
  have eq76087 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq76076
       have r₂ := eq27
       grind)
    | exact resolve eq76076 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76076
  have eq76179 : (σ y) ≠ (σ y) ∨ (M.op (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq76087 eq13
    | (have j0 := eq13 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (σ y)
       have r₂ := eq76087
       grind)
    | exact resolve eq13 eq76087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76087
  have eq76186 : (M.op (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq76179
  have eq76194 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq74781 eq76186
    | exact resolve eq76186 eq74781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76186
  have eq76301 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq76194 eq75732
    | exact resolve eq75732 eq76194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75732 eq76194
  have eq76316 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq76301
  have eq76322 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq76316
       have r₂ := eq27
       grind)
    | exact resolve eq76316 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76316
  have eq76337 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq76322 eq27
    | exact resolve eq27 eq76322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq77023 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ y)) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq75528 eq53
    | exact resolve eq53 eq75528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq77036 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq74781 eq77023
    | exact resolve eq77023 eq74781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74781 eq77023
  have eq77042 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq76322 eq77036
    | exact resolve eq77036 eq76322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76322 eq77036
  have eq77698 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq77042 eq75528
    | exact resolve eq75528 eq77042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75528 eq77042
  have eq77708 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq77698
  have eq77712 : y = (M.op y x) := by
    first
    | (have r₁ := eq77708
       have r₂ := eq76337
       grind)
    | exact resolve eq77708 eq76337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77708
  have eq77725 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq77712
       grind)
    | exact superpose eq77712 eq14
    | exact resolve eq14 eq77712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77738 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq77725 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq77725
    | (have j0 := eq77725 X0
       grind)
    | exact resolve eq77725 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq77725
  have eq77747 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq74498 eq77738
    | exact resolve eq77738 eq74498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74498 eq77738
  have eq78841 : x = (M.op y x) := by
    first
    | (have i₁ := eq77747 y
       have i₂ := eq77712
       grind)
    | exact superpose eq77712 eq77747
    | exact resolve eq77747 eq77712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77747
  have eq78860 : x = y := by
    first
    | (have i₁ := eq78841
       have i₂ := eq77712
       grind)
    | exact superpose eq77712 eq78841
    | exact resolve eq78841 eq77712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77712 eq78841
  have eq78863 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq78860
       grind)
    | exact superpose eq78860 eq24
    | exact resolve eq24 eq78860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq78860
  have eq79192 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq78863
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq78863
    | exact resolve eq78863 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq78863
  have eq79309 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq74741 eq79192
    | exact resolve eq79192 eq74741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74741 eq79192
  have eq79393 : False := by grind
  exact eq79393

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pxy_pyx_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
    intro X0 X1 X2
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
  have eq51 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq83 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq70
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq70
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq83
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq83
    | exact resolve eq83 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq89
    | exact resolve eq89 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq90
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq90
    | exact resolve eq90 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq105 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq105 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq105
    | (have j0 := eq105 (σ X0)
       grind)
    | exact resolve eq105 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq105 x
       grind)
    | exact superpose eq105 eq44
    | (have j1 := eq105 x
       grind)
    | exact resolve eq44 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq416 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X0 X2)) (M.op X4 (M.op X3 X4))) = (M.op (M.op X5 (M.op X0 (M.op X1 (M.op X2 X1)))) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 X3 X5 (M.op X3 (M.op X0 X2)) X4
       have i₂ := eq53 X2 X3 X0 X1
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op y X0))) = (M.op (M.op X1 (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 y X1 x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 y X1 x X0
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 (M.op (σ y) X0))) = (M.op (M.op X1 (M.op (σ x) (σ y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ y) X1 (σ x) X0
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq426 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X0 X1) x X1 X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X0) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 x
       have i₂ := eq53 X2 X0 X1 x
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq803 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq426 X2 (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq426
    | exact resolve eq426 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq805 : ∀ X0 : G, (M.op (M.op y (M.op x y)) (M.op X0 x)) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq426
    | exact resolve eq426 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq806 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op X0 (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq52 eq426
    | exact resolve eq426 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq827 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 x) X0)) := by
    intro X0
    first
    | exact superpose eq805 eq426
    | exact resolve eq426 eq805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805
  have eq840 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq806 eq426
    | exact resolve eq426 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426 eq806
  have eq861 : ∀ X0 : G, y = (M.op (M.op (M.op X0 (M.op x y)) X0) x) := by
    intro X0
    first
    | (have i₁ := eq431 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq431
    | (have j0 := eq431 X0 x y
       grind)
    | exact resolve eq431 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq865 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq27 eq431
    | (have j0 := eq431 X0 (σ x) (σ y)
       grind)
    | exact resolve eq431 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq949 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 y) X0) := by
    intro X0
    first
    | exact superpose eq827 eq14
    | exact resolve eq14 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq971 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq840 eq14
    | exact resolve eq14 eq840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq15461 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq334 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq32743 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op x y)) X0) x) = (M.op (M.op X1 (M.op (M.op X2 y) X2)) (M.op X3 (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq416 (M.op X2 y) y X2 X1 X3 x
       have i₂ := eq419 (M.op X2 y) X0
       grind)
    | exact superpose eq419 eq416
    | exact resolve eq416 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq32746 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) X0) (σ x)) = (M.op (M.op X1 (M.op (M.op X2 (σ y)) X2)) (M.op X3 (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq420 eq416
    | exact resolve eq416 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416 eq420
  have eq33228 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) X0) (σ x)) = (M.op (M.op X1 (M.op (M.op (σ x) (σ y)) (σ x))) (M.op X3 (M.op X1 X3))) := by
    intro X0 X1 X3
    first
    | exact superpose eq971 eq32746
    | (have j0 := eq32746 X0 X1 (σ x) X3
       grind)
    | exact resolve eq32746 eq971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971 eq32746
  have eq33231 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 (M.op x y)) X0) x) = (M.op (M.op X1 (M.op (M.op x y) x)) (M.op X3 (M.op X1 X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq32743 X0 X1 x X3
       have i₂ := eq949 x
       grind)
    | (have i₁ := eq32743 X0 X1 x X3
       have i₂ := eq949 X0
       grind)
    | exact superpose eq949 eq32743
    | (have j0 := eq32743 X0 X1 x X3
       grind)
    | exact resolve eq32743 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949 eq32743
  have eq33557 : ∀ X1 X3 : G, (σ y) = (M.op (M.op X1 (M.op (M.op (σ x) (σ y)) (σ x))) (M.op X3 (M.op X1 X3))) := by
    intro X1 X3
    first
    | exact superpose eq865 eq33228
    | exact resolve eq33228 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865 eq33228
  have eq33558 : ∀ X1 X3 : G, y = (M.op (M.op X1 (M.op (M.op x y) x)) (M.op X3 (M.op X1 X3))) := by
    intro X1 X3
    first
    | exact superpose eq861 eq33231
    | exact resolve eq33231 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861 eq33231
  have eq125547 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq91 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125548 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq125547
    | exact resolve eq125547 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125547
  have eq125559 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq125548
       have r₂ := eq28
       grind)
    | exact resolve eq125548 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125548
  have eq125561 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq125559
    | exact resolve eq125559 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125559
  have eq125702 : (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq125561 eq33557
    | exact resolve eq33557 eq125561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125561
  have eq125707 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq125702
       have i₂ := eq803 sF4 sF2 sF2
       grind)
    | exact superpose eq803 eq125702
    | exact resolve eq125702 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125702
  have eq125839 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq125707
  have eq126062 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq125839
    | exact resolve eq125839 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125839
  have eq126903 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq126062 eq91
    | exact resolve eq91 eq126062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq126062
  have eq126911 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq126903
  have eq126913 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq126911
       have r₂ := eq28
       grind)
    | exact resolve eq126911 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126911
  have eq127305 : y = (M.op (M.op x (M.op (M.op x y) x)) (M.op x (M.op x y))) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq33558 x x
       have i₂ := eq126913
       grind)
    | exact superpose eq126913 eq33558
    | exact resolve eq33558 eq126913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33558 eq126913
  have eq127309 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq127305
       have i₂ := eq803 sF0 x x
       grind)
    | exact superpose eq803 eq127305
    | exact resolve eq127305 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127305
  have eq127431 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq127309
  have eq127651 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq127431
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq127431
    | exact resolve eq127431 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127431
  have eq128643 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq127651
       grind)
    | exact superpose eq127651 eq70
    | exact resolve eq70 eq127651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq127651
  have eq128661 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq128643
    | exact resolve eq128643 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128643
  have eq129370 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq128661 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq128661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129373 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq129370
    | exact resolve eq129370 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129370
  have eq129384 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq129373
       have r₂ := eq28
       grind)
    | exact resolve eq129373 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129373
  have eq129386 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq129384
    | exact resolve eq129384 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129384
  have eq311483 : (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq129386 eq33557
    | exact resolve eq33557 eq129386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33557 eq129386
  have eq311490 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq311483
       have i₂ := eq803 sF4 sF2 sF2
       grind)
    | exact superpose eq803 eq311483
    | exact resolve eq311483 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803 eq311483
  have eq311491 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq311490
  have eq311713 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq311491
  have eq312047 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq311713
    | exact resolve eq311713 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311713
  have eq312171 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq312047 eq128661
    | exact resolve eq128661 eq312047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128661 eq312047
  have eq312173 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq312171
  have eq312181 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq312173
       have r₂ := eq28
       grind)
    | exact resolve eq312173 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312173
  have eq312184 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq312181 eq30
    | exact resolve eq30 eq312181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq312181
  have eq312427 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq312184
    | exact resolve eq312184 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq312184
  have eq312428 : x = y := by grind
  clear eq312427
  have eq312434 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq312428
       grind)
    | exact superpose eq312428 eq19
    | exact resolve eq19 eq312428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq312435 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq312428
       grind)
    | exact superpose eq312428 eq25
    | exact resolve eq25 eq312428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq312428
  have eq312683 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq312435
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq312435
    | exact resolve eq312435 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312435
  have eq312696 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq312683 eq27
    | exact resolve eq27 eq312683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq312683
  have eq312997 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq338
       have i₂ := eq312434
       grind)
    | exact superpose eq312434 eq338
    | exact resolve eq338 eq312434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq313042 : (k (M.op x y) x) = (M.op x (M.op x y)) := by grind
  have eq313361 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq312997
    | exact resolve eq312997 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312997
  have eq313508 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq316074 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq313361 eq105
    | (have j0 := eq105 (σ x)
       grind)
    | exact resolve eq105 eq313361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq316075 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq312696 eq316074
    | exact resolve eq316074 eq312696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316074
  have eq316087 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq316075
       have r₂ := eq28
       grind)
    | exact resolve eq316075 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316075
  have eq316093 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq312696 eq316087
    | exact resolve eq316087 eq312696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316087
  have eq316235 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq316093 eq313508
    | exact resolve eq313508 eq316093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313508 eq316093
  have eq316238 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq312696 eq316235
    | exact resolve eq316235 eq312696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316235
  have eq316738 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq316238 eq313361
    | exact resolve eq313361 eq316238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313361 eq316238
  have eq316742 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq316738
  have eq316746 : x = (M.op x y) := by
    first
    | (have r₁ := eq316742
       have r₂ := eq28
       grind)
    | exact resolve eq316742 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316742
  have eq316754 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq316746 eq21
    | exact resolve eq21 eq316746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq317072 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq316746 eq313042
    | exact resolve eq313042 eq316746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313042
  have eq317077 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq317072
       have i₂ := eq312434
       grind)
    | exact superpose eq312434 eq317072
    | exact resolve eq317072 eq312434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312434 eq317072
  have eq317257 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq316754
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq316754
    | exact resolve eq316754 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316754
  have eq317260 : x = (k x x) := by
    first
    | exact superpose eq316746 eq317077
    | exact resolve eq317077 eq316746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316746 eq317077
  have eq318596 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq15461 x
       have i₂ := eq317260
       grind)
    | exact superpose eq317260 eq15461
    | (have j0 := eq15461 x
       grind)
    | exact resolve eq15461 eq317260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15461 eq317260
  have eq318600 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq318596
  have eq318610 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq318600
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq318600
    | exact resolve eq318600 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq318600
  have eq318622 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq312696 eq318610
    | exact resolve eq318610 eq312696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312696 eq318610
  have eq318633 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq317257 eq318622
    | exact resolve eq318622 eq317257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317257 eq318622
  have eq318642 : False := by grind
  exact eq318642

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_pxy_pyx_Equation2373 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2373 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  have eq54 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq14 X0 X2 X3
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
  have eq89 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq89
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq89
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq96
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq96
    | exact resolve eq96 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq103 : (M.op y x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq102
    | exact resolve eq102 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq218 : ∀ X0 X1 : G, (M.op X1 (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op X0 (M.op X1 (σ x))) X0) := by
    intro X0 X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq699 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0)) X3) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3 (M.op X1 X2)
       have i₂ := eq55 X1 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq8070 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op (M.op X0 X1) X0)) (M.op (σ y) (M.op (σ x) (σ y)))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq218 eq699
    | exact resolve eq699 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq699
  have eq131646 : y = (M.op (M.op (σ x) (M.op (M.op y x) y)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8070 y y
       have i₂ := eq103
       grind)
    | exact superpose eq103 eq8070
    | exact resolve eq8070 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq131661 : x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq8070 eq131646
    | exact resolve eq131646 eq8070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131646
  have eq131662 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq131661
  have eq131733 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq131662 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq131662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131662
  have eq131740 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq131733
    | exact resolve eq131733 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131733
  have eq131751 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq131740
       have r₂ := eq28
       grind)
    | exact resolve eq131740 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131740
  have eq131885 : (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ y) (σ x)) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq131751 eq8070
    | exact resolve eq8070 eq131751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131751
  have eq131901 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq8070 eq131885
    | exact resolve eq131885 eq8070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8070 eq131885
  have eq131902 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq131901
  have eq131952 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq131902 eq30
    | exact resolve eq30 eq131902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq131902
  have eq132177 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq131952
    | exact resolve eq131952 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq131952
  have eq132178 : x = y := by grind
  clear eq132177
  have eq132489 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq132178
       grind)
    | exact superpose eq132178 eq19
    | exact resolve eq19 eq132178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq132490 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq132178
       grind)
    | exact superpose eq132178 eq25
    | exact resolve eq25 eq132178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq132178
  have eq132712 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq132490
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq132490
    | exact resolve eq132490 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq132490
  have eq132742 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq132712 eq27
    | exact resolve eq27 eq132712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq132712
  have eq134054 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq132742 eq68
    | exact resolve eq68 eq132742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq132742
  have eq134315 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq134054
       have i₂ := eq132489
       grind)
    | exact superpose eq132489 eq134054
    | exact resolve eq134054 eq132489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132489 eq134054
  have eq134408 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq134315 eq15
    | exact resolve eq15 eq134315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134315
  have eq134488 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq134408
    | exact resolve eq134408 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq134408
  have eq134509 : False := by grind
  exact eq134509

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_pyy_pxy_Equation2373 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2373 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq9 X0 (M.op X1 (M.op X2 X1)) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
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
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq37 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq38 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq29
    | (have j0 := eq29 X0 X1
       grind)
    | exact resolve eq29 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq72 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) = (M.op (M.op X2 (M.op X1 (σ X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (σ X0) X2 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) (M.op X4 (M.op X3 X4)))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq25 X3 (M.op X1 X2) X2 X4
       have i₂ := eq24 X1 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq24 eq25
    | exact resolve eq25 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X3)) X0)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X3 X1 X2 x
       have i₂ := eq24 X3 X0 (M.op X1 (M.op X2 X1)) x
       grind)
    | exact superpose eq24 eq25
    | exact resolve eq25 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq239 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = (M.op X1 X1) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq38
    | (have j0 := eq38 X0 X1
       have j1 := eq37 X0 X1
       grind)
    | exact resolve eq38 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq38
  have eq2031 : ∀ X0 X1 X2 X3 : G, (σ X1) = (M.op X2 (M.op (M.op (M.op X0 (M.op (σ (M.op X1 X1)) (σ X1))) X0) (M.op X3 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X2 (σ (M.op X1 X1)) (σ X1) X3
       have i₂ := eq72 X1 (σ (M.op X1 X1)) X0
       grind)
    | exact superpose eq72 eq25
    | exact resolve eq25 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq72
  have eq77969 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq239 x y
       grind)
    | exact superpose eq239 eq16
    | (have j1 := eq239 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq239 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq239 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq239 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq78672 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq77969
  have eq79304 : ∀ X0 X1 X2 : G, (σ y) = (M.op X0 (M.op (M.op (M.op X1 (M.op (σ (M.op x x)) (σ x))) X1) (M.op X2 (M.op X0 X2)))) ∨ (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq112 X1 (σ x) (σ y) X0 X2
       have i₂ := eq78672
       grind)
    | exact superpose eq78672 eq112
    | exact resolve eq112 eq78672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78672
  have eq79433 : (σ x) = (σ y) ∨ (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq79304 x x x
       have i₂ := eq2031 x x x x
       grind)
    | exact superpose eq2031 eq79304
    | exact resolve eq79304 eq2031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2031 eq79304
  have eq79434 : (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq79433
  have eq95351 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq79434
       grind)
    | exact superpose eq79434 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq79434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79434
  have eq95412 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq95351
  have eq125636 : ∀ X0 X1 : G, y = (M.op X0 (M.op (M.op X1 (M.op (M.op y (M.op x y)) X0)) X1)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq121 X1 y y X0
       have i₂ := eq95412
       grind)
    | exact superpose eq95412 eq121
    | exact resolve eq121 eq95412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95412
  have eq125738 : x = y ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq125636 x x
       have i₂ := eq121 x y x x
       grind)
    | exact superpose eq121 eq125636
    | exact resolve eq125636 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq125636
  have eq125739 : (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq125738
  have eq152457 : ∀ X0 X1 X2 : G, y = (M.op X0 (M.op (M.op (M.op X1 (M.op (M.op x x) x)) X1) (M.op X2 (M.op X0 X2)))) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq112 X1 x y X0 X2
       have i₂ := eq125739
       grind)
    | exact superpose eq125739 eq112
    | exact resolve eq112 eq125739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125739
  have eq152667 : x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq152457 x x x
       have i₂ := eq112 x x x x x
       grind)
    | exact superpose eq112 eq152457
    | exact resolve eq152457 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq152457
  have eq152668 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq152667
  have eq190745 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq152668
       grind)
    | exact superpose eq152668 eq10
    | exact resolve eq10 eq152668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152668
  have eq190841 : x = y ∨ x = y := by
    first
    | (have i₁ := eq190745
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq190745
    | exact resolve eq190745 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190745
  have eq190842 : x = y := by grind
  clear eq190841
  have eq212239 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq190842
       grind)
    | exact superpose eq190842 eq16
    | exact resolve eq16 eq190842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190842
  have eq212240 : False := by grind
  exact eq212240

/-- `Equation2420`: `x = (y ◇ (z ◇ (w ◇ y))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_y_pyx_Equation2420 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2420 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2420.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 (M.op X3 X1))) X0) = X0 := by
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
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
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
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
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
  have eq174 : ∀ X0 X1 : G, (M.op (M.op y (M.op X0 (M.op x y))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X1 y X0 x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X1 (σ y) X0 (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X5 : G, (M.op (M.op X1 (M.op X0 X1)) X5) = X5 := by
    intro X0 X1 X5
    first
    | (have i₁ := eq16 X5 X1 (M.op x (M.op x (M.op x x))) X0
       have i₂ := eq16 (M.op X0 X1) x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : x ≠ (M.op x y) ∨ (k y x) = (M.op y x) := by
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
  have eq180 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X1 : G, (M.op (M.op y (M.op x y)) X1) = X1 := by
    intro X1
    first
    | exact superpose eq174 eq174
    | exact resolve eq174 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq196 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq183 eq175
    | exact resolve eq175 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq965 : x ≠ (M.op x y) ∨ y = (M.op y x) ∨ y = (k x y) := by
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
  have eq966 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq999 : (M.op x y) = (k y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
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
  have eq1000 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1007 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1058 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1094 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1007 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq1007 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq1007 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq1007 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq1130 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq999
       grind)
    | exact superpose eq999 eq39
    | exact resolve eq39 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1131 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1130
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1130
    | exact resolve eq1130 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130
  have eq1133 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1131
    | exact resolve eq1131 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131
  have eq1586 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1133 eq1000
    | exact resolve eq1000 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1593 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1586
       have r₂ := eq27
       grind)
    | exact resolve eq1586 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1586
  have eq1598 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1593 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1593
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1593
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1593
       grind)
    | exact resolve eq12 eq1593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1593
  have eq1606 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq1598
  have eq1611 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1606
    | exact resolve eq1606 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1606
  have eq1612 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq1611
  have eq1643 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1612 eq107
    | exact resolve eq107 eq1612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1612
  have eq1650 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1643
    | exact resolve eq1643 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1643
  have eq1653 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq999 eq1650
    | exact resolve eq1650 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999 eq1650
  have eq1654 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1653
  have eq1660 : y ≠ y ∨ x = (M.op x y) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1654
       grind)
    | exact superpose eq1654 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1654
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1654
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1654
       grind)
    | exact resolve eq12 eq1654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1661 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1654
       grind)
    | exact superpose eq1654 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1654
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1654
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1654
       grind)
    | exact resolve eq13 eq1654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1663 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq177 y x X0
       have i₂ := eq1654
       grind)
    | exact superpose eq1654 eq177
    | exact resolve eq177 eq1654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1654
  have eq1667 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1661
  have eq1668 : x = (M.op x y) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1660
  have eq1671 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1663 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1663
    | (have j0 := eq1663 X0
       grind)
    | exact resolve eq1663 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1663
  have eq1672 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1667
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1667
    | exact resolve eq1667 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1667
  have eq1673 : x = (M.op x y) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1668
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1668
    | exact resolve eq1668 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1668
  have eq1674 : x = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1673
  have eq1723 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1672
       grind)
    | exact superpose eq1672 eq40
    | exact resolve eq40 eq1672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672
  have eq1724 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1723
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1723
    | exact resolve eq1723 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1723
  have eq1726 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1724
    | exact resolve eq1724 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1724
  have eq1730 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq1674
       grind)
    | exact superpose eq1674 eq36
    | exact resolve eq36 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1674
  have eq1735 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1730
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1730
    | exact resolve eq1730 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1730
  have eq1752 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1735 eq1000
    | exact resolve eq1000 eq1735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1735
  have eq1756 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1752
  have eq1764 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1756
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq1756
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq1756 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1766 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1756 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1756
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1756
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1756
       grind)
    | exact resolve eq13 eq1756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1756
  have eq1772 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1766
  have eq1777 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1772
    | exact resolve eq1772 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1772
  have eq1778 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq1764
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq1764
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq1764
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq1764 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1764
  have eq1779 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1726 eq1777
    | exact resolve eq1777 eq1726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726 eq1777
  have eq1780 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq1778
       have r₂ := eq966
       grind)
    | exact resolve eq1778 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966 eq1778
  have eq1781 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1779
       have r₂ := eq27
       grind)
    | exact resolve eq1779 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1779
  have eq1782 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1781 eq27
    | exact resolve eq27 eq1781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1784 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1781 eq180
    | (have r₁ := eq180
       have r₂ := eq1781
       grind)
    | exact resolve eq180 eq1781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1785 : ∀ X0 : G, (M.op (M.op (σ y) (σ x)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1781 eq196
    | exact resolve eq196 eq1781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq1792 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1784
  have eq2802 : (τ (σ y)) = (k x (τ (σ y))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1780 eq90
    | exact resolve eq90 eq1780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq2813 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq31 eq2802
    | exact resolve eq2802 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2802
  have eq2828 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq2813 eq1792
    | exact resolve eq1792 eq2813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2829 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (k x y) := by
    intro X0
    first
    | exact superpose eq2813 eq1785
    | exact resolve eq1785 eq2813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1785
  have eq2832 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq2813 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2813
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2813
       grind)
    | exact resolve eq13 eq2813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2834 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = X0 ∨ x = (M.op x y) ∨ y = (k x y) := by
    intro X0
    first
    | exact superpose eq2813 eq177
    | exact resolve eq177 eq2813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2813
  have eq2839 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (k x y) := by grind
  clear eq2832
  have eq2842 : ∀ X0 : G, y = (k x y) ∨ x = (M.op x y) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2829 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2829
  have eq2843 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (k x y) := by grind
  clear eq2828
  have eq2848 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = X0 ∨ x = (M.op x y) ∨ y = (k x y) := by
    intro X0
    first
    | exact superpose eq26 eq2834
    | (have j0 := eq2834 X0
       grind)
    | exact resolve eq2834 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2834
  have eq2849 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq26 eq2839
    | exact resolve eq2839 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2839
  have eq2854 : ∀ X0 : G, y = (k x y) ∨ x = (M.op x y) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1781 eq2848
    | exact resolve eq2848 eq1781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2848
  have eq2855 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq1781 eq2849
    | exact resolve eq2849 eq1781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2849
  have eq2865 : ∀ X0 : G, (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq35 y
       have i₂ := eq2842 X0
       grind)
    | exact superpose eq2842 eq35
    | (have j1 := eq2842 X0
       grind)
    | exact resolve eq35 eq2842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2842
  have eq2874 : ∀ X0 : G, (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2865 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2865
    | (have j0 := eq2865 X0
       grind)
    | exact resolve eq2865 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2865
  have eq2882 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq2843 eq1133
    | exact resolve eq1133 eq2843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133 eq2843
  have eq2899 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ y = (k x y) := by grind
  clear eq2882
  have eq2905 : y = (k x y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq2899
       have r₂ := eq965
       grind)
    | exact resolve eq2899 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2899
  have eq2913 : ∀ X0 : G, y ≠ y ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1058 y x
       have i₂ := eq2854 X0
       grind)
    | exact superpose eq2854 eq1058
    | (have j0 := eq1058 y x
       have j1 := eq2854 X0
       grind)
    | (have r₁ := eq1058 y x
       have r₂ := eq2854 X0
       grind)
    | exact resolve eq1058 eq2854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2914 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2913 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2913
  have eq2917 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2914 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2914
    | (have j0 := eq2914 X0
       grind)
    | exact resolve eq2914 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2914
  have eq2918 : ∀ X0 : G, y = (M.op y x) ∨ x = (M.op x y) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2917 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2917
  have eq2930 : (τ (σ x)) = (k (τ (σ x)) y) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq2855 eq152
    | exact resolve eq152 eq2855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq2855
  have eq2938 : y = (k x y) ∨ x = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq29 eq2930
    | exact resolve eq2930 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2930
  have eq3026 : y ≠ y ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1058 y x
       have i₂ := eq2905
       grind)
    | exact superpose eq2905 eq1058
    | (have j0 := eq1058 y x
       grind)
    | (have r₁ := eq1058 y x
       have r₂ := eq2905
       grind)
    | exact resolve eq1058 eq2905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2905
  have eq3027 : y ≠ y ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq3026
  have eq3028 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq3027
  have eq3029 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq3028
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3028
    | exact resolve eq3028 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3028
  have eq3035 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq3029
       grind)
    | exact superpose eq3029 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq3029
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3029
       grind)
    | exact resolve eq13 eq3029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3029
  have eq3042 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq3035
  have eq3047 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq3042
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3042
    | exact resolve eq3042 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3042
  have eq3119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq3047
       grind)
    | exact superpose eq3047 eq40
    | exact resolve eq40 eq3047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3047
  have eq3127 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq3119
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3119
    | exact resolve eq3119 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3119
  have eq3129 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq3127
    | exact resolve eq3127 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3127
  have eq3152 : ∀ X0 : G, y ≠ y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1094 x y
       have i₂ := eq2854 X0
       grind)
    | exact superpose eq2854 eq1094
    | (have j0 := eq1094 x y
       have j1 := eq2854 X0
       grind)
    | (have r₁ := eq1094 x y
       have r₂ := eq2854 X0
       grind)
    | exact resolve eq1094 eq2854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2854
  have eq3191 : ∀ X0 : G, y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3152 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3152
  have eq3198 : ∀ X0 : G, y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3191 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3191
    | (have j0 := eq3191 X0
       grind)
    | exact resolve eq3191 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3191
  have eq3204 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3198 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3198
    | (have j0 := eq3198 X0
       grind)
    | exact resolve eq3198 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3198
  have eq3205 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq3204 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3204
  have eq3503 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3205 eq26
    | (have j1 := eq3205 (σ y)
       grind)
    | exact resolve eq26 eq3205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3567 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1781 eq3503
    | exact resolve eq3503 eq1781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1781 eq3503
  have eq3598 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3567 eq1792
    | exact resolve eq1792 eq3567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1792
  have eq3619 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq3598
  have eq3631 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3205 eq3619
    | exact resolve eq3619 eq3205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3205 eq3619
  have eq4029 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3567 eq3129
    | exact resolve eq3129 eq3567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3129 eq3567
  have eq4052 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq4029
  have eq4061 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq4052
       have r₂ := eq1782
       grind)
    | exact resolve eq4052 eq1782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4052
  have eq4066 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3631 eq4061
    | exact resolve eq4061 eq3631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3631 eq4061
  have eq4069 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4066
       have r₂ := eq1782
       grind)
    | exact resolve eq4066 eq1782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4066
  have eq4073 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq4069
       grind)
    | exact superpose eq4069 eq24
    | exact resolve eq24 eq4069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4121 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq4073
    | exact resolve eq4073 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4073
  have eq4132 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4121 eq1782
    | exact resolve eq1782 eq4121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1782
  have eq4135 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq4132
  have eq4569 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = X0 ∨ x = (M.op x y) ∨ (M.op (σ x) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq177 y x X0
       have i₂ := eq2918 X1
       grind)
    | exact superpose eq2918 eq177
    | (have j1 := eq2918 X1
       grind)
    | exact resolve eq177 eq2918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq2918
  have eq4584 : ∀ X0 X1 : G, (M.op (σ x) X1) = X1 ∨ x = (M.op x y) ∨ (M.op (M.op x y) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4569 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4569
    | (have j0 := eq4569 X0 X1
       grind)
    | exact resolve eq4569 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4569
  have eq4954 : y ≠ y ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1058 y x
       have i₂ := eq2938
       grind)
    | exact superpose eq2938 eq1058
    | (have j0 := eq1058 y x
       grind)
    | (have r₁ := eq1058 y x
       have r₂ := eq2938
       grind)
    | exact resolve eq1058 eq2938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2938
  have eq4956 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x y) := by grind
  clear eq4954
  have eq4965 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq4956
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4956
    | exact resolve eq4956 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4956
  have eq4966 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (k x y) := by grind
  clear eq4965
  have eq4974 : x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (k x y) := by
    first
    | exact superpose eq4069 eq4966
    | exact resolve eq4966 eq4069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4966
  have eq4978 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq4069 eq4974
    | exact resolve eq4974 eq4069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4069 eq4974
  have eq5667 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq4584 (M.op sF2 sF3) x
       grind)
    | exact superpose eq4584 eq26
    | (have j1 := eq4584 X0 (σ y)
       grind)
    | exact resolve eq26 eq4584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4584
  have eq5744 : ∀ X0 : G, (σ x) = (σ y) ∨ x = (M.op x y) ∨ (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1671 eq5667
    | (have j0 := eq5667 X0
       have j1 := eq1671 X0
       grind)
    | exact resolve eq5667 eq1671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1671 eq5667
  have eq5746 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq5744 X0
       grind)
    | (have r₁ := eq5744 X0
       have r₂ := eq4135
       grind)
    | exact resolve eq5744 eq4135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5744
  have eq6260 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq4978 eq5746
    | exact resolve eq5746 eq4978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4978 eq5746
  have eq6278 : x = (k x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq6260
  have eq6289 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6278 eq41
    | exact resolve eq41 eq6278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq6278
  have eq6296 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6289
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6289
    | exact resolve eq6289 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6289
  have eq6298 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4121 eq6296
    | exact resolve eq6296 eq4121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4121 eq6296
  have eq6314 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6298 eq1780
    | exact resolve eq1780 eq6298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1780
  have eq6315 : ∀ X0 : G, (σ x) = (σ y) ∨ x = (M.op x y) ∨ (M.op (σ y) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6298 eq2874
    | (have j0 := eq2874 X0
       grind)
    | exact resolve eq2874 eq6298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2874 eq6298
  have eq6329 : ∀ X0 : G, (σ x) = (σ y) ∨ x = (M.op x y) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq6315 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6315
  have eq6330 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq6314
  have eq6345 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq6329 X0
       grind)
    | (have r₁ := eq6329 X0
       have r₂ := eq4135
       grind)
    | exact resolve eq6329 eq4135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6329
  have eq6346 : x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq6330
       have r₂ := eq4135
       grind)
    | exact resolve eq6330 eq4135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6330
  have eq6353 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6345 eq6346
    | exact resolve eq6346 eq6345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6345 eq6346
  have eq6357 : x = (M.op x y) := by
    first
    | (have r₁ := eq6353
       have r₂ := eq4135
       grind)
    | exact resolve eq6353 eq4135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4135 eq6353
  have eq6359 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq6357
       grind)
    | exact superpose eq6357 eq18
    | exact resolve eq18 eq6357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq6360 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq6357
       grind)
    | exact superpose eq6357 eq22
    | exact resolve eq22 eq6357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq6361 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq6357
       grind)
    | exact superpose eq6357 eq35
    | exact resolve eq35 eq6357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq6362 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq6357
       grind)
    | exact superpose eq6357 eq39
    | exact resolve eq39 eq6357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq6363 : (M.op x y) ≠ (M.op x y) ∨ (k y (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq179
       have i₂ := eq6357
       grind)
    | exact superpose eq6357 eq179
    | (have r₁ := eq179
       have r₂ := eq6357
       grind)
    | exact resolve eq179 eq6357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq6364 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op y (M.op x y)) ∨ y = (k (M.op x y) y) := by
    first
    | (have i₁ := eq965
       have i₂ := eq6357
       grind)
    | exact superpose eq6357 eq965
    | (have r₁ := eq965
       have r₂ := eq6357
       grind)
    | exact resolve eq965 eq6357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965
  have eq6367 : y = (k (M.op x y) y) ∨ y = (M.op y (M.op x y)) := by grind
  clear eq6364
  have eq6368 : (k y (M.op x y)) = (M.op y (M.op x y)) := by grind
  clear eq6363
  have eq6370 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq6360 eq20
    | exact resolve eq20 eq6360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6469 : ∀ X0 : G, (M.op (k y (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq6368 eq183
    | exact resolve eq183 eq6368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6478 : y ≠ (k y (M.op x y)) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq6368 eq13
    | (have j0 := eq13 (M.op x y) y
       grind)
    | exact resolve eq13 eq6368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6488 : y ≠ (k y (M.op x y)) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq6359 eq6478
    | exact resolve eq6478 eq6359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6478
  have eq7991 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y (M.op x y)) := by
    first
    | exact superpose eq6367 eq6361
    | exact resolve eq6361 eq6367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6361 eq6367
  have eq8003 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq7991
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7991
    | exact resolve eq7991 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7991
  have eq8008 : (σ y) = (k (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq6368 eq8003
    | exact resolve eq8003 eq6368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6368 eq8003
  have eq8032 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq8008 eq1094
    | (have j0 := eq1094 (σ x) (σ y)
       grind)
    | (have r₁ := eq1094 (σ x) (σ y)
       have r₂ := eq8008
       grind)
    | exact resolve eq1094 eq8008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094
  have eq8033 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq8008 eq1058
    | (have j0 := eq1058 (σ y) (σ x)
       grind)
    | (have r₁ := eq1058 (σ y) (σ x)
       have r₂ := eq8008
       grind)
    | exact resolve eq1058 eq8008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058 eq8008
  have eq8034 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y (M.op x y)) := by grind
  clear eq8033
  have eq8035 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by grind
  clear eq8032
  have eq8038 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq26 eq8034
    | exact resolve eq8034 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8034
  have eq8039 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq26 eq8035
    | exact resolve eq8035 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8035
  have eq8045 : y = (k y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq8039
    | exact resolve eq8039 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8039
  have eq8735 : y ≠ y ∨ (M.op x y) = (k (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8045 eq6488
    | (have r₁ := eq6488
       have r₂ := eq8045
       grind)
    | exact resolve eq6488 eq8045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6488
  have eq8737 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8045 eq6362
    | exact resolve eq6362 eq8045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6362 eq8045
  have eq8743 : (M.op x y) = (k (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8735
  have eq8748 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8737
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8737
    | exact resolve eq8737 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8737
  have eq8884 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8743 eq40
    | exact resolve eq40 eq8743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq8743
  have eq8893 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq8884
    | exact resolve eq8884 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq8884
  have eq8902 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6370 eq8893
    | exact resolve eq8893 eq6370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8893
  have eq8919 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8748 eq1000
    | exact resolve eq1000 eq8748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000 eq8748
  have eq8939 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8919
  have eq9189 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8939 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq8939
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq8939
       grind)
    | exact resolve eq13 eq8939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8939
  have eq9202 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9189
  have eq9211 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq9202
    | exact resolve eq9202 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9202
  have eq9217 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8902 eq9211
    | exact resolve eq9211 eq8902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8902 eq9211
  have eq9218 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9217
  have eq9232 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9218
  have eq12277 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq8038 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq8038
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq8038
       grind)
    | exact resolve eq12 eq8038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8038
  have eq12292 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by grind
  clear eq12277
  have eq12297 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq26 eq12292
    | exact resolve eq12292 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq12292
  have eq12298 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by grind
  clear eq12297
  have eq12684 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq12298 eq107
    | exact resolve eq107 eq12298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq12298
  have eq12698 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq29 eq12684
    | exact resolve eq12684 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq12684
  have eq12704 : (M.op x y) = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | (have i₁ := eq12698
       have i₂ := eq6357
       grind)
    | exact superpose eq6357 eq12698
    | exact resolve eq12698 eq6357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6357 eq12698
  have eq12765 : ∀ X0 : G, y = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq12704 eq6469
    | exact resolve eq6469 eq12704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12704
  have eq13475 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6469 X0
       have i₂ := eq12765 (k y sF0)
       grind)
    | exact superpose eq12765 eq6469
    | (have j1 := eq12765 X1
       grind)
    | exact resolve eq6469 eq12765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6469 eq12765
  have eq13921 : ∀ X0 : G, (M.op y X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq6359
       have i₂ := eq13475 (M.op sF0 y) x
       grind)
    | exact superpose eq13475 eq6359
    | (have j1 := eq13475 X0 x
       grind)
    | exact resolve eq6359 eq13475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13475
  have eq14062 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq183 x
       have i₂ := eq13921 sF0
       grind)
    | exact superpose eq13921 eq183
    | exact resolve eq183 eq13921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq13921
  have eq14248 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14062 eq6359
    | exact resolve eq6359 eq14062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6359 eq14062
  have eq14355 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq14248
  have eq14375 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14355 eq27
    | exact resolve eq27 eq14355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14355
  have eq14387 : y = (M.op x y) := by
    first
    | (have r₁ := eq14375
       have r₂ := eq6370
       grind)
    | exact resolve eq14375 eq6370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14375
  have eq14391 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq14387
       grind)
    | exact superpose eq14387 eq24
    | exact resolve eq24 eq14387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq14387
  have eq14480 : (σ x) = (σ y) := by
    first
    | exact superpose eq6360 eq14391
    | exact resolve eq14391 eq6360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6360 eq14391
  have eq14553 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14480 eq9232
    | (have r₁ := eq9232
       have r₂ := eq14480
       grind)
    | exact resolve eq9232 eq14480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9232 eq14480
  have eq14564 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14553
  have eq14617 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq14564 eq27
    | exact resolve eq27 eq14564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq14564
  have eq14636 : False := by grind
  exact eq14636

/-- `Equation2452`: `x = (x ◇ ((x ◇ y) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_x_pyx_Equation2452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq21 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op (M.op X0 x) x) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq34 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq37 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27
    | exact resolve eq27 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 X2 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq27
    | exact resolve eq27 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq46 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op X0 (M.op (M.op X0 X1) X2))) = X0 ∨ (M.op (M.op X0 (M.op (M.op X0 X1) X2)) (M.op X0 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X0 (M.op (M.op X0 X1) X2))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X0 (M.op X0 (M.op (M.op X0 X1) X2))
       grind)
    | (have r₁ := eq13 X0 (M.op X0 (M.op (M.op X0 X1) X2))
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X0 X1) X2)) (M.op X0 (M.op (M.op X0 X1) X2))) = X0 ∨ (k X0 (M.op X0 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq46 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq74 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq107 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76 X0 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq76
    | exact resolve eq76 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X0) = (k X0 (M.op X0 (M.op (M.op X0 X1) X2))) ∨ (k X0 (M.op X0 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    grind
  clear eq49
  have eq252 : ∀ X0 X1 X2 : G, (k X0 (M.op X0 (M.op (M.op X0 X1) X2))) = X0 ∨ (k X0 (M.op X0 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq250 X0 X1 X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq250
    | (have j0 := eq250 X0 X1 X2
       grind)
    | exact resolve eq250 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq253 : ∀ X0 X1 X2 : G, (k X0 (M.op X0 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq252 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq265 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq253 X0 X0 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq253
    | exact resolve eq253 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq253
  have eq309 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq265 (σ X0)
       grind)
    | exact superpose eq265 eq34
    | exact resolve eq34 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq310 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq265 (τ X0)
       grind)
    | exact superpose eq265 eq18
    | exact resolve eq18 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq314 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq310 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq310
    | exact resolve eq310 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq315 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq309 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq309
    | exact resolve eq309 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq334 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq314 (τ X0)
       grind)
    | exact superpose eq314 eq18
    | exact resolve eq18 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq341 : ∀ X0 : G, (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq334 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq334
    | exact resolve eq334 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq395 : ∀ X0 : G, (k X0 (τ (σ (k X0 X0)))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq315 X0
       have i₂ := eq76 X0 X0
       grind)
    | exact superpose eq76 eq315
    | (have j1 := eq76 X0 X0
       grind)
    | exact resolve eq315 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq407 : ∀ X0 : G, (k X0 (τ (σ (k X0 X0)))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq395 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq414 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq407 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq407
    | (have j0 := eq407 X0
       grind)
    | exact resolve eq407 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq432 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))
       have i₂ := eq341 (τ X0)
       grind)
    | exact superpose eq341 eq18
    | exact resolve eq18 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq439 : ∀ X0 : G, (k X0 (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq432 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq432
    | exact resolve eq432 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq655 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq74 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq74
    | exact resolve eq74 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq668 : ∀ X0 X1 X2 : G, (τ (k X2 (k (σ X0) X1))) = (k (τ X2) (M.op (τ X1) X0)) ∨ (M.op (τ X1) X0) = X0 ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 X2 (M.op (τ X1) X0)
       have i₂ := eq74 X1 X0
       grind)
    | exact superpose eq74 eq27
    | (have j1 := eq74 X1 X0
       grind)
    | exact resolve eq27 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq74
  have eq684 : ∀ X0 X1 X2 : G, (M.op (τ X1) X0) = X0 ∨ (k (τ X2) (k X0 (τ X1))) = (k (τ X2) (M.op (τ X1) X0)) ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq668 X0 X1 X2
       have i₂ := eq39 X0 X1 X2
       grind)
    | exact superpose eq39 eq668
    | (have j0 := eq668 X0 X1 X2
       grind)
    | exact resolve eq668 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq692 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq655 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq655
    | (have j0 := eq655 X0 X1
       grind)
    | exact resolve eq655 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq1023 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq116 (τ X1) (τ X0)
       have i₂ := eq37 X1 X0
       grind)
    | exact superpose eq37 eq116
    | (have j0 := eq116 (τ X1) (τ X0)
       grind)
    | exact resolve eq116 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq1038 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1023 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1023
    | (have j0 := eq1023 X0 X1
       grind)
    | exact resolve eq1023 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023
  have eq1044 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1038 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1038
    | (have j0 := eq1038 X0 X1
       grind)
    | exact resolve eq1038 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038
  have eq1047 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1044 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1044
    | (have j0 := eq1044 X0 X1
       grind)
    | exact resolve eq1044 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq1048 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1047 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1047
    | (have j0 := eq1047 X0 X1
       grind)
    | exact resolve eq1047 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047
  have eq1049 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1048 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1048
    | (have j0 := eq1048 X0 X1
       grind)
    | exact resolve eq1048 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048
  have eq1050 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1049 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1049
    | (have j0 := eq1049 X0 X1
       grind)
    | exact resolve eq1049 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049
  have eq1732 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k X0 (σ X1)) (σ X2)
       have i₂ := eq107 X0 X1 X2
       grind)
    | exact superpose eq107 eq13
    | (have j0 := eq13 (k X0 (σ X1)) (σ X2)
       have j1 := eq107 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k X0 (σ X1)) (σ X2)
       have r₂ := eq107 X0 X1 X2
       grind)
    | exact resolve eq13 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1740 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1732 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1732
  have eq1741 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (k (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1740 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1740
  have eq1742 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (k (k (τ X0) X1) X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1741 X0 X1 X2
       have i₂ := eq26 X0 X1 X2
       grind)
    | exact superpose eq26 eq1741
    | (have j0 := eq1741 X0 X1 X2
       grind)
    | exact resolve eq1741 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1741
  have eq2250 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0))))))))
       have i₂ := eq439 (τ X0)
       grind)
    | exact superpose eq439 eq18
    | exact resolve eq18 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq2265 : ∀ X0 : G, (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2250 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2250
    | exact resolve eq2250 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2250
  have eq4435 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq414 X0
       grind)
    | exact superpose eq414 eq41
    | (have j1 := eq414 X0
       grind)
    | exact resolve eq41 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq414
  have eq4462 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq4435 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4435
    | (have j0 := eq4435 X0
       grind)
    | exact resolve eq4435 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4435
  have eq4498 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq315 X0
       have i₂ := eq4462 X0
       grind)
    | exact superpose eq4462 eq315
    | (have j1 := eq4462 X0
       grind)
    | exact resolve eq315 eq4462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315 eq4462
  have eq4515 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq4498 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4498
  have eq4643 : ∀ X0 X1 X2 : G, (k (k X1 X0) (τ X2)) = (τ (k (σ (M.op X0 X1)) X2)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 (k X1 X0) X2
       have i₂ := eq692 X0 X1
       grind)
    | exact superpose eq692 eq34
    | (have j1 := eq692 X0 X1
       grind)
    | exact resolve eq34 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq4690 : ∀ X0 X1 X2 : G, (k (k X1 X0) (τ X2)) = (k (M.op X0 X1) (τ X2)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4643 X0 X1 X2
       have i₂ := eq34 (M.op X0 X1) X2
       grind)
    | exact superpose eq34 eq4643
    | (have j0 := eq4643 X0 X1 X2
       grind)
    | exact resolve eq4643 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq4643
  have eq14515 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (M.op (τ (τ (τ (τ (τ X0))))) (τ (τ (τ (τ (τ X0)))))))))))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ (τ X0))))) (τ (τ (τ (τ (τ X0))))))))))
       have i₂ := eq2265 (τ X0)
       grind)
    | exact superpose eq2265 eq18
    | exact resolve eq18 eq2265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2265
  have eq14561 : ∀ X0 : G, (k X0 (σ (σ (σ (σ (σ (M.op (τ (τ (τ (τ (τ X0))))) (τ (τ (τ (τ (τ X0)))))))))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14515 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14515
    | exact resolve eq14515 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14515
  have eq33834 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k (τ X1) (k (τ X0) (τ X0))) = (k (τ X1) (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq684 (τ X0) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq33835 : ∀ X0 X1 : G, (k (τ X1) (k (τ X0) (τ X0))) = (k (τ X1) (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq33834 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33834
  have eq33842 : ∀ X0 X1 : G, (k (τ X1) (τ (k X0 X0))) = (k (τ X1) (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq33835 X0 X1
       have i₂ := eq37 X0 X0
       grind)
    | exact superpose eq37 eq33835
    | (have j0 := eq33835 X0 X1
       grind)
    | exact resolve eq33835 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33835
  have eq33868 : ∀ X0 X1 : G, (τ (k X1 (k X0 X0))) = (k (τ X1) (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq33842 X0 X1
       have i₂ := eq37 (k X0 X0) X1
       grind)
    | exact superpose eq37 eq33842
    | (have j0 := eq33842 X0 X1
       grind)
    | exact resolve eq33842 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33842
  have eq65888 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1742 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1742
  have eq65889 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq65888 X0 X1 X2
       have j1 := eq107 X0 X1 X2
       grind)
    | (have r₁ := eq65888 X0 X1 X2
       have r₂ := eq107 X0 X1 X2
       grind)
    | exact resolve eq65888 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq65888
  have eq98615 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (σ (M.op (τ (τ (τ (τ (τ (τ X0)))))) (τ (τ (τ (τ (τ (τ X0)))))))))))))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (σ (σ (σ (σ (σ (M.op (τ (τ (τ (τ (τ (τ X0)))))) (τ (τ (τ (τ (τ (τ X0))))))))))))
       have i₂ := eq14561 (τ X0)
       grind)
    | exact superpose eq14561 eq18
    | exact resolve eq18 eq14561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98705 : ∀ X0 : G, (k X0 (σ (σ (σ (σ (σ (σ (M.op (τ (τ (τ (τ (τ (τ X0)))))) (τ (τ (τ (τ (τ (τ X0)))))))))))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq98615 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq98615
    | exact resolve eq98615 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98615
  have eq252586 : ∀ X0 X1 X2 : G, (k (k X1 X2) X0) = (k (M.op X2 X1) X0) ∨ (M.op X2 X1) = X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4690 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4690
    | (have j0 := eq4690 X2 X1 X2
       grind)
    | exact resolve eq4690 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4690
  have eq431551 : ∀ X0 X1 : G, (τ (k X1 (k (σ X0) (σ X0)))) = (k (τ X1) (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq33868 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33868
    | exact resolve eq33868 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33868
  have eq431732 : ∀ X0 X1 : G, (k (τ X1) (k X0 (τ (σ X0)))) = (k (τ X1) (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq431551 X0 X1
       have i₂ := eq39 X0 (σ X0) X1
       grind)
    | exact superpose eq39 eq431551
    | (have j0 := eq431551 X0 X1
       grind)
    | exact resolve eq431551 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq431551
  have eq431776 : ∀ X0 X1 : G, (k (τ X1) (k X0 X0)) = (k (τ X1) (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq431732 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq431732
    | (have j0 := eq431732 X0 X1
       grind)
    | exact resolve eq431732 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431732
  have eq432749 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 (k X1 X1)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq431776 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq431776
    | (have j0 := eq431776 X1 X1
       grind)
    | exact resolve eq431776 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431776
  have eq433660 : ∀ X0 X1 : G, (k X0 (σ (σ (τ (τ X0))))) = X0 ∨ (k X1 (k (τ (τ X0)) (τ (τ X0)))) = (k X1 (M.op (τ (τ X0)) (τ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq341 X0
       have i₂ := eq432749 X1 (τ (τ X0))
       grind)
    | exact superpose eq432749 eq341
    | (have j1 := eq432749 X1 (τ (τ X0))
       grind)
    | exact resolve eq341 eq432749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341 eq432749
  have eq433732 : ∀ X0 X1 : G, (k X0 (σ (τ X0))) = X0 ∨ (k X1 (k (τ (τ X0)) (τ (τ X0)))) = (k X1 (M.op (τ (τ X0)) (τ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq433660 X0 X1
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq433660
    | (have j0 := eq433660 X0 X1
       grind)
    | exact resolve eq433660 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433660
  have eq433925 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X1 (k (τ (τ X0)) (τ (τ X0)))) = (k X1 (M.op (τ (τ X0)) (τ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq433732 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq433732
    | (have j0 := eq433732 X0 X1
       grind)
    | exact resolve eq433732 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433732
  have eq433966 : ∀ X0 X1 : G, (k X1 (τ (k (τ X0) (τ X0)))) = (k X1 (M.op (τ (τ X0)) (τ (τ X0)))) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq433925 X0 X1
       have i₂ := eq37 (τ X0) (τ X0)
       grind)
    | exact superpose eq37 eq433925
    | (have j0 := eq433925 X0 X1
       grind)
    | exact resolve eq433925 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433925
  have eq433984 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X1 (τ (τ (k X0 X0)))) = (k X1 (M.op (τ (τ X0)) (τ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq433966 X0 X1
       have i₂ := eq37 X0 X0
       grind)
    | exact superpose eq37 eq433966
    | (have j0 := eq433966 X0 X1
       grind)
    | exact resolve eq433966 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433966
  have eq526806 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 (M.op (τ (τ X0)) (τ (τ X0)))) = (k X1 (τ (τ (M.op X0 X0)))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq433984 X1 X1
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq433984
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq433984 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq527020 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 (τ (τ (k X0 X0)))) = (k X1 (M.op (τ (τ X0)) (τ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1050 X0 X0
       have i₂ := eq433984 X0 X1
       grind)
    | exact superpose eq433984 eq1050
    | (have j0 := eq1050 X0 X0
       have j1 := eq433984 X0 X1
       grind)
    | (have r₁ := eq1050 X0 X0
       have r₂ := eq433984 X0 X1
       grind)
    | exact resolve eq1050 eq433984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050 eq433984
  have eq527294 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 (τ (τ (k X0 X0)))) = (k X1 (M.op (τ (τ X0)) (τ (τ X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq527020 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527020
  have eq527295 : ∀ X0 X1 : G, (k X1 (τ (τ (k X0 X0)))) = (k X1 (M.op (τ (τ X0)) (τ (τ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq527294 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527294
  have eq527318 : ∀ X0 X1 : G, (k X1 (M.op (τ (τ X0)) (τ (τ X0)))) = (k X1 (τ (τ (M.op X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq526806 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526806
  have eq552400 : ∀ X0 X1 : G, (k X0 (τ (τ (k X1 X1)))) = (k X0 (τ (τ (M.op X1 X1)))) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq527295 X1 X0
       have i₂ := eq527318 X1 X0
       grind)
    | exact superpose eq527318 eq527295
    | (have j0 := eq527295 X1 X1
       have j1 := eq527318 X1 X1
       grind)
    | exact resolve eq527295 eq527318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527295 eq527318
  have eq553096 : ∀ X0 X1 : G, (k X0 (τ (τ (k X1 X1)))) = (k X0 (τ (τ (M.op X1 X1)))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq552400 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552400
  have eq557643 : ∀ X0 X1 : G, (k X0 (σ (τ (τ (k X1 X1))))) = (σ (k (τ X0) (τ (τ (M.op X1 X1))))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ (τ (k X1 X1)))
       have i₂ := eq553096 (τ X0) X1
       grind)
    | exact superpose eq553096 eq18
    | (have j1 := eq553096 X0 X1
       grind)
    | exact resolve eq18 eq553096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553096
  have eq557950 : ∀ X0 X1 : G, (k X0 (σ (τ (τ (k X1 X1))))) = (k (σ (τ X0)) (τ (M.op X1 X1))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq557643 X0 X1
       have i₂ := eq19 (τ (M.op X1 X1)) (τ X0)
       grind)
    | exact superpose eq19 eq557643
    | (have j0 := eq557643 X0 X1
       grind)
    | exact resolve eq557643 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557643
  have eq558706 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = (k X0 (σ (τ (τ (k X1 X1))))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq557950 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq557950
    | (have j0 := eq557950 X0 X1
       grind)
    | exact resolve eq557950 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557950
  have eq559407 : ∀ X0 X1 : G, (k X0 (τ (k X1 X1))) = (k X0 (τ (M.op X1 X1))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq558706 X0 X1
       have i₂ := eq11 (τ (k X1 X1))
       grind)
    | exact superpose eq11 eq558706
    | (have j0 := eq558706 X0 X1
       grind)
    | exact resolve eq558706 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558706
  have eq561838 : ∀ X0 : G, (τ (k X0 X0)) = (k (τ (k X0 X0)) (k (τ (k X0 X0)) (τ (M.op X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4515 (τ (k X0 X0))
       have i₂ := eq559407 (τ (k X0 X0)) X0
       grind)
    | exact superpose eq559407 eq4515
    | (have j1 := eq559407 X0 X0
       grind)
    | exact resolve eq4515 eq559407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559407
  have eq562925 : ∀ X0 : G, (τ (k X0 X0)) = (k (τ (k X0 X0)) (τ (k (k X0 X0) (M.op X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq561838 X0
       have i₂ := eq37 (M.op X0 X0) (k X0 X0)
       grind)
    | exact superpose eq37 eq561838
    | (have j0 := eq561838 X0
       grind)
    | exact resolve eq561838 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561838
  have eq563626 : ∀ X0 : G, (τ (k X0 X0)) = (τ (k (k X0 X0) (k (k X0 X0) (M.op X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq562925 X0
       have i₂ := eq37 (k (k X0 X0) (M.op X0 X0)) (k X0 X0)
       grind)
    | exact superpose eq37 eq562925
    | (have j0 := eq562925 X0
       grind)
    | exact resolve eq562925 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562925
  have eq672231 : ∀ X0 : G, (σ (τ (k X0 X0))) = (k (k X0 X0) (k (k X0 X0) (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k (k X0 X0) (k (k X0 X0) (M.op X0 X0)))
       have i₂ := eq563626 X0
       grind)
    | exact superpose eq563626 eq11
    | (have j1 := eq563626 X0
       grind)
    | exact resolve eq11 eq563626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563626
  have eq672593 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (k (k X0 X0) (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq672231 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq672231
    | (have j0 := eq672231 X0
       grind)
    | exact resolve eq672231 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672231
  have eq672812 : ∀ X0 : G, (k X0 X0) = (k (M.op X0 X0) (k (k X0 X0) (M.op X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq252586 (k (k X0 X0) (M.op X0 X0)) X0 X0
       have i₂ := eq672593 X0
       grind)
    | exact superpose eq672593 eq252586
    | (have j0 := eq252586 X0 X0 X0
       have j1 := eq672593 X0
       grind)
    | exact resolve eq252586 eq672593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672593
  have eq672849 : ∀ X0 : G, (k X0 X0) = (k (M.op X0 X0) (k (k X0 X0) (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq672812 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672812
  have eq674418 : ∀ X0 : G, (k X0 X0) = (k (M.op X0 X0) (k (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq672849 X0
       have i₂ := eq252586 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq252586 eq672849
    | (have j0 := eq672849 X0
       have j1 := eq252586 X0 X0 X0
       grind)
    | exact resolve eq672849 eq252586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252586 eq672849
  have eq674459 : ∀ X0 : G, (k X0 X0) = (k (M.op X0 X0) (k (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq674418 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674418
  have eq674466 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq674459 X0
       have i₂ := eq4515 (M.op X0 X0)
       grind)
    | exact superpose eq4515 eq674459
    | (have j0 := eq674459 X0
       grind)
    | exact resolve eq674459 eq4515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4515 eq674459
  have eq675131 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq674466 (σ X0)
       grind)
    | exact superpose eq674466 eq15
    | (have j1 := eq674466 (σ X0)
       grind)
    | exact resolve eq15 eq674466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674466
  have eq681578 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  clear eq675131
  have eq681755 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq681578 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq681578
    | (have j0 := eq681578 X0
       grind)
    | exact resolve eq681578 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681578
  have eq681756 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq681755 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681755
  have eq681924 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq681756 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq681756
    | exact resolve eq681756 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682404 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq682790 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq682404 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq682404
    | exact resolve eq682404 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682404
  have eq682983 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq681924 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq681924
    | exact resolve eq681924 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq681924
  have eq683135 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq682983 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq682983
    | exact resolve eq682983 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682983
  have eq687199 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0 X0
       have i₂ := eq683135 (τ X0)
       grind)
    | exact superpose eq683135 eq37
    | exact resolve eq37 eq683135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq687335 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq687199 X0
       have i₂ := eq683135 X0
       grind)
    | exact superpose eq683135 eq687199
    | exact resolve eq687199 eq683135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687199
  have eq713715 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq682790 X0
       have i₂ := eq683135 X0
       grind)
    | exact superpose eq683135 eq682790
    | exact resolve eq682790 eq683135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682790
  have eq714368 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq713715
  have eq1679334 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) (k X0 (σ (σ (σ (σ (σ (σ (M.op (τ (τ (τ (τ (τ (τ X0)))))) (τ (τ (τ (τ (τ (τ X0))))))))))))))) ∨ (M.op (σ X1) (σ X1)) = (k X0 (σ (σ (σ (σ (σ (σ (M.op (τ (τ (τ (τ (τ (τ X0)))))) (τ (τ (τ (τ (τ (τ X0)))))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq65889 X0 (σ (σ (σ (σ (σ (M.op (τ (τ (τ (τ (τ (τ X0)))))) (τ (τ (τ (τ (τ (τ X0)))))))))))) X1
       have i₂ := eq14561 (τ X0)
       grind)
    | exact superpose eq14561 eq65889
    | (have j0 := eq65889 X0 (σ (σ (σ (σ (σ (M.op (τ (τ (τ (τ (τ (τ X0)))))) (τ (τ (τ (τ (τ (τ X0)))))))))))) X1
       grind)
    | exact resolve eq65889 eq14561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14561 eq65889
  have eq1681970 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) (σ X1)) = (k X0 (σ (σ (σ (σ (σ (σ (M.op (τ (τ (τ (τ (τ (τ X0)))))) (τ (τ (τ (τ (τ (τ X0)))))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1679334 X0 X1
       have i₂ := eq98705 X0
       grind)
    | exact superpose eq98705 eq1679334
    | (have j0 := eq1679334 X0 X1
       grind)
    | exact resolve eq1679334 eq98705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1679334
  have eq1683443 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) (σ X1)) = (k X0 (σ (σ (σ (σ (σ (σ (M.op (τ (τ (τ (τ (τ (τ X0)))))) (τ (τ (τ (τ (τ (τ X0)))))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1681970 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq1681970
    | (have j0 := eq1681970 X0 X1
       grind)
    | exact resolve eq1681970 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1681970
  have eq1684525 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1683443 X0 X1
       have i₂ := eq98705 X0
       grind)
    | exact superpose eq98705 eq1683443
    | (have j0 := eq1683443 X0 X1
       grind)
    | exact resolve eq1683443 eq98705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98705 eq1683443
  have eq1685377 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1684525 X0 X1
       have i₂ := eq681756 X1
       grind)
    | exact superpose eq681756 eq1684525
    | (have j0 := eq1684525 X0 X1
       grind)
    | exact resolve eq1684525 eq681756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681756 eq1684525
  have eq1686002 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1685377 X0 X1
       have i₂ := eq683135 X1
       grind)
    | exact superpose eq683135 eq1685377
    | (have j0 := eq1685377 X0 X1
       grind)
    | exact resolve eq1685377 eq683135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683135 eq1685377
  have eq1688260 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1686002 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1686002
    | (have j0 := eq1686002 X1 (τ X0)
       grind)
    | exact resolve eq1686002 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1689061 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1686002 (σ X1) X0
       grind)
    | exact superpose eq1686002 eq15
    | (have j1 := eq1686002 (σ X1) X0
       grind)
    | exact resolve eq15 eq1686002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1686002
  have eq1689883 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1688260 X0 X1
       have i₂ := eq687335 X0
       grind)
    | exact superpose eq687335 eq1688260
    | (have j0 := eq1688260 X0 X1
       grind)
    | exact resolve eq1688260 eq687335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687335 eq1688260
  have eq1690346 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1689883 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq1689883
    | (have j0 := eq1689883 X0 X1
       grind)
    | exact resolve eq1689883 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1689883
  have eq1692833 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq1690346 X0 (τ X1)
       grind)
    | exact superpose eq1690346 eq18
    | (have j1 := eq1690346 X0 (τ X1)
       grind)
    | exact resolve eq18 eq1690346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1690346
  have eq1715816 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1692833 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1692833
    | exact resolve eq1692833 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1692833
  have eq1717587 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1715816 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1715816
    | (have j0 := eq1715816 X0 X1
       grind)
    | exact resolve eq1715816 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1715816
  have eq1739172 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1689061 x y
       grind)
    | exact superpose eq1689061 eq16
    | (have j1 := eq1689061 x y
       grind)
    | exact resolve eq16 eq1689061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1689061
  have eq1742701 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1739172
       have i₂ := eq1717587 y x
       grind)
    | exact superpose eq1717587 eq1739172
    | (have j1 := eq1717587 y x
       grind)
    | (have r₁ := eq1739172
       have r₂ := eq1717587 y x
       grind)
    | exact resolve eq1739172 eq1717587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1717587 eq1739172
  have eq1742704 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq1742701
  have eq1745736 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq714368 x
       have i₂ := eq1742704
       grind)
    | exact superpose eq1742704 eq714368
    | exact resolve eq714368 eq1742704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1742704
  have eq1746008 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq1745736
       have r₂ := eq16
       grind)
    | exact resolve eq1745736 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1745736
  have eq1746385 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1746008
       grind)
    | exact superpose eq1746008 eq10
    | exact resolve eq10 eq1746008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1746008
  have eq1747644 : y = (M.op x x) := by
    first
    | (have i₁ := eq1746385
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1746385
    | exact resolve eq1746385 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1746385
  have eq1751434 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq714368 x
       have i₂ := eq1747644
       grind)
    | exact superpose eq1747644 eq714368
    | exact resolve eq714368 eq1747644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714368 eq1747644
  have eq1751705 : False := by grind
  exact eq1751705
