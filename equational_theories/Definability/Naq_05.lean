import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4425`: `x ◇ (x ◇ y) = (z ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_x_x_pxy_Equation4425 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4425 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4425.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
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
  clear eq45
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
  have eq175 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : y ≠ (M.op x y) ∨ x = (k x y) := by
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
  have eq177 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq91 (M.op sF2 sF2)
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq91
    | exact resolve eq91 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq175
  have eq202 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq30 eq191
    | exact resolve eq191 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq693 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
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
  have eq720 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op X0 (M.op X0 X1))) := by
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
  have eq721 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (M.op X3 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq693 X1 X2 X3 (M.op X3 x)
       have i₂ := eq16 X3 x X0
       grind)
    | exact superpose eq16 eq693
    | exact resolve eq693 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq725 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
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
  have eq726 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq693
    | (have j0 := eq693 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq693 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq734 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X4 X4) X4) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq16 X2 (M.op X2 x) X4
       have i₂ := eq693 X2 x X0 X1
       grind)
    | (have i₁ := eq16 X2 (M.op X2 x) X4
       have i₂ := eq693 X0 X1 X2 x
       grind)
    | exact superpose eq693 eq16
    | exact resolve eq16 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq736 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq725 x x
       have i₂ := eq726 x x
       grind)
    | (have i₁ := eq725 (σ x) (σ y)
       have i₂ := eq726 x x
       grind)
    | exact superpose eq726 eq725
    | (have j0 := eq725 (σ x) (σ y)
       have j1 := eq726 x y
       grind)
    | exact resolve eq725 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq740 : ∀ X0 X3 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X3 (M.op (M.op X0 X0) X0)) := by
    intro X0 X3
    first
    | (have i₁ := eq721 X0 x x X3
       have i₂ := eq726 x x
       grind)
    | (have i₁ := eq721 X0 (σ x) (σ y) X3
       have i₂ := eq726 X0 x
       grind)
    | exact superpose eq726 eq721
    | (have j0 := eq721 X0 (σ x) (σ y) X3
       grind)
    | exact resolve eq721 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq741 : ∀ X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq720 x x X2 X3 X4
       have i₂ := eq726 x x
       grind)
    | (have i₁ := eq720 (σ x) (σ y) X2 X3 X4
       have i₂ := eq726 x x
       grind)
    | exact superpose eq726 eq720
    | (have j0 := eq720 (σ x) (σ y) X2 X3 X4
       grind)
    | exact resolve eq720 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq751 : ∀ X4 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X4 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X4
    first
    | (have i₁ := eq741 x x X4
       have i₂ := eq726 x x
       grind)
    | (have i₁ := eq741 (σ x) (σ y) X4
       have i₂ := eq726 x x
       grind)
    | exact superpose eq726 eq741
    | (have j0 := eq741 (σ x) (σ y) X4
       grind)
    | exact resolve eq741 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq775 : ∀ X2 : G, (M.op (M.op X2 X2) X2) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X2
    first
    | (have i₁ := eq16 x x X2
       have i₂ := eq726 x x
       grind)
    | (have i₁ := eq16 (σ x) (σ y) X2
       have i₂ := eq726 x x
       grind)
    | exact superpose eq726 eq16
    | (have j0 := eq16 (σ x) (σ y) X2
       grind)
    | exact resolve eq16 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq802 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq751 eq28
    | (have j0 := eq28 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq28 x (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq751 x
       grind)
    | exact resolve eq28 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq806 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have j0 := eq802 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq820 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq822 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq853 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq854 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq855 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq854 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq923 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq806 eq35
    | exact resolve eq35 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq937 : ∀ X0 : G, (k X0 (σ (M.op (σ x) (M.op (σ x) (σ y))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq923 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq923
    | exact resolve eq923 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq984 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (σ x) (M.op (σ x) (σ y)))))) := by
    intro X0
    first
    | exact superpose eq937 eq35
    | exact resolve eq35 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1004 : ∀ X0 : G, (k X0 (σ (σ (M.op (σ x) (M.op (σ x) (σ y)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq984 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq984
    | exact resolve eq984 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984
  have eq1084 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op (σ x) (M.op (σ x) (σ y))))))) := by
    intro X0
    first
    | exact superpose eq1004 eq35
    | exact resolve eq35 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq1104 : ∀ X0 : G, (k X0 (σ (σ (σ (M.op (σ x) (M.op (σ x) (σ y))))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1084 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq1084
    | exact resolve eq1084 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1185 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (M.op (σ x) (M.op (σ x) (σ y)))))))) := by
    intro X0
    first
    | exact superpose eq1104 eq35
    | exact resolve eq35 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq1205 : ∀ X0 : G, (k X0 (σ (σ (σ (σ (M.op (σ x) (M.op (σ x) (σ y)))))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1185 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq1185
    | exact resolve eq1185 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185
  have eq1427 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq820
       grind)
    | exact superpose eq820 eq41
    | exact resolve eq41 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1429 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1427
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1427
    | exact resolve eq1427 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1427
  have eq1431 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq1429
    | exact resolve eq1429 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429
  have eq1559 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (M.op (σ x) (M.op (σ x) (σ y))))))))) := by
    intro X0
    first
    | exact superpose eq1205 eq35
    | exact resolve eq35 eq1205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1560 : (σ x) = (k (σ x) (σ (σ (σ (σ (σ (M.op (σ x) (M.op (σ x) (σ y))))))))) := by
    first
    | exact superpose eq1205 eq36
    | exact resolve eq36 eq1205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205
  have eq1578 : (σ x) = (k (σ x) (σ (σ (σ (σ (σ (M.op (σ x) (M.op (σ x) (σ y))))))))) := by
    first
    | (have i₁ := eq1560
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1560
    | exact resolve eq1560 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1560
  have eq1579 : ∀ X0 : G, (k X0 (σ (σ (σ (σ (σ (M.op (σ x) (M.op (σ x) (σ y))))))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1559 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq1559
    | exact resolve eq1559 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1559
  have eq2397 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1431 eq822
    | exact resolve eq822 eq1431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2405 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq2397
       have r₂ := eq27
       grind)
    | exact resolve eq2397 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2397
  have eq2410 : x = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2405 eq202
    | exact resolve eq202 eq2405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq2405
  have eq2444 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq2410
    | exact resolve eq2410 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2410
  have eq2450 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq2444
       have r₂ := eq176
       grind)
    | exact resolve eq2444 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq2444
  have eq2453 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq2450
       have r₂ := eq13 x y
       grind)
    | exact resolve eq2450 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2450
  have eq2457 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq2453
       grind)
    | exact superpose eq2453 eq41
    | exact resolve eq41 eq2453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq2453
  have eq2458 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2457
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2457
    | exact resolve eq2457 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2457
  have eq2460 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq2458
       have r₂ := eq177
       grind)
    | exact resolve eq2458 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq2458
  have eq2464 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2460 eq1431
    | exact resolve eq1431 eq2460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1431
  have eq2465 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2460 eq822
    | exact resolve eq822 eq2460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq2468 : (τ (σ x)) = (k (τ (σ x)) y) := by
    first
    | exact superpose eq2460 eq153
    | exact resolve eq153 eq2460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq2469 : x = (k x y) := by
    first
    | exact superpose eq30 eq2468
    | exact resolve eq2468 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2468
  have eq2474 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq820
       have i₂ := eq2469
       grind)
    | exact superpose eq2469 eq820
    | exact resolve eq820 eq2469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820 eq2469
  have eq2480 : y = (k x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2464
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq2464
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq2464 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2494 : y = (k x x) ∨ x = y ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq2464
       grind)
    | exact superpose eq2464 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq2464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2499 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq726 x x
       have i₂ := eq2464
       grind)
    | exact superpose eq2464 eq726
    | exact resolve eq726 eq2464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2464
  have eq2501 : y = (k x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2494
  have eq2502 : y = (k x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) := by grind
  clear eq2480
  have eq2504 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2499
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2499
    | exact resolve eq2499 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2499
  have eq2538 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2465 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq2465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2543 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2465 eq726
    | exact resolve eq726 eq2465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2544 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq2465 eq734
    | exact resolve eq734 eq2465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2545 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2538
  have eq2547 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq2544
    | (have j0 := eq2544 X0 X1
       grind)
    | exact resolve eq2544 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2544
  have eq2548 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq2543
    | exact resolve eq2543 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2543
  have eq2559 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq2547 x X1
       have i₂ := eq775 x
       grind)
    | exact superpose eq775 eq2547
    | exact resolve eq2547 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2547
  have eq2564 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op X1 (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq2548 eq2559
    | exact resolve eq2559 eq2548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2559
  have eq2582 : y = (k x x) ∨ x = y ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq2474
       grind)
    | exact superpose eq2474 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq2474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2587 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq726 x x
       have i₂ := eq2474
       grind)
    | exact superpose eq2474 eq726
    | exact resolve eq726 eq2474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2474
  have eq2589 : y = (k x x) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2582
  have eq2592 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2587
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2587
    | exact resolve eq2587 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2587
  have eq2616 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq2504 eq806
    | exact resolve eq806 eq2504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq2623 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq2504 eq937
    | exact resolve eq937 eq2504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2685 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq20 eq2623
    | (have j0 := eq2623 X0
       grind)
    | exact resolve eq2623 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2623
  have eq2783 : ∀ X0 : G, (k X0 (σ (M.op (σ x) (σ y)))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2548 eq937
    | exact resolve eq937 eq2548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2992 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2592 eq2564
    | exact resolve eq2564 eq2592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3136 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2685 eq855
    | (have j0 := eq855 (σ (M.op x y))
       grind)
    | (have r₁ := eq855 (σ (M.op x y))
       have r₂ := eq2685 (σ (M.op x y))
       grind)
    | exact resolve eq855 eq2685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2685
  have eq3150 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3136
  have eq3268 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3150 eq726
    | exact resolve eq726 eq3150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3273 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2504 eq3268
    | exact resolve eq3268 eq2504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2504 eq3268
  have eq3352 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3273 eq3150
    | exact resolve eq3150 eq3273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3150 eq3273
  have eq3374 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq3352
  have eq3404 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq3374 eq29
    | exact resolve eq29 eq3374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3374
  have eq3439 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq3404
    | exact resolve eq3404 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3404
  have eq3556 : (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3439 eq29
    | exact resolve eq29 eq3439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3954 : (σ (M.op (σ x) (σ y))) ≠ (σ (M.op (σ x) (σ y))) ∨ (σ (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ x) (σ y))) (σ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2783 eq855
    | (have j0 := eq855 (σ (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq855 (σ (M.op (σ x) (σ y)))
       have r₂ := eq2783 (σ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq855 eq2783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2783
  have eq3968 : (σ (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ x) (σ y))) (σ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3954
  have eq6420 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ (M.op (σ x) (σ y))) (σ (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq3968 eq740
    | exact resolve eq740 eq3968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq6442 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ (M.op (σ x) (σ y))) (σ (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2548 eq6420
    | exact resolve eq6420 eq2548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2548 eq6420
  have eq6458 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq3968 eq6442
    | exact resolve eq6442 eq3968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6442
  have eq6516 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6458 eq3968
    | exact resolve eq3968 eq6458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3968 eq6458
  have eq6518 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6516
  have eq7792 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2992 eq2592
    | exact resolve eq2592 eq2992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2992
  have eq7801 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7792
  have eq7805 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq7801
    | exact resolve eq7801 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7801
  have eq7806 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq7805
  have eq8147 : (M.op x y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7806 eq2592
    | exact resolve eq2592 eq7806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8150 : (M.op x y) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq7806
  have eq8153 : (M.op x y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq8147
  have eq8248 : (M.op x y) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8153 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq8153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8153
  have eq8256 : (M.op x y) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq8248
  have eq8268 : (M.op x y) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8256
       have r₂ := eq8150
       grind)
    | exact resolve eq8256 eq8150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8150 eq8256
  have eq8303 : (k x x) = (τ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8268 eq98
    | exact resolve eq98 eq8268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8268
  have eq8323 : (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3556 eq8303
    | exact resolve eq8303 eq3556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3556 eq8303
  have eq8365 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2589
       have i₂ := eq8323
       grind)
    | exact superpose eq8323 eq2589
    | exact resolve eq2589 eq8323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2589 eq8323
  have eq8385 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq8365
  have eq8405 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8385 eq27
    | exact resolve eq27 eq8385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8385
  have eq8538 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq8405
       have r₂ := eq3439
       grind)
    | exact resolve eq8405 eq3439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3439 eq8405
  have eq8559 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq8538
       grind)
    | exact superpose eq8538 eq18
    | exact resolve eq18 eq8538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8560 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq8538
       grind)
    | exact superpose eq8538 eq24
    | exact resolve eq24 eq8538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8538
  have eq8586 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq8560
    | exact resolve eq8560 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8560
  have eq8587 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq736 eq8559
    | exact resolve eq8559 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8559
  have eq8588 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2592 eq8587
    | exact resolve eq8587 eq2592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2592 eq8587
  have eq8589 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq8588
  have eq8607 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8589 eq751
    | exact resolve eq751 eq8589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8616 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8589 eq937
    | exact resolve eq937 eq8589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8651 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8589 eq2564
    | exact resolve eq2564 eq8589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8685 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq8616
    | (have j0 := eq8616 X0
       grind)
    | exact resolve eq8616 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8616
  have eq8849 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8685 eq855
    | (have j0 := eq855 (σ (M.op x y))
       grind)
    | (have r₁ := eq855 (σ (M.op x y))
       have r₂ := eq8685 (σ (M.op x y))
       grind)
    | exact resolve eq855 eq8685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8685
  have eq8868 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq8849
  have eq8928 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8868 eq726
    | exact resolve eq726 eq8868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8938 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8589 eq8928
    | exact resolve eq8928 eq8589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8928
  have eq8975 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8938 eq8868
    | exact resolve eq8868 eq8938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8868 eq8938
  have eq8999 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq8975
  have eq9034 : (M.op x y) = (τ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8999 eq29
    | exact resolve eq29 eq8999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq9288 : (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq8586 eq8999
    | exact resolve eq8999 eq8586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8586
  have eq9289 : (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq9288
  have eq9462 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq9289 eq26
    | exact resolve eq26 eq9289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9289
  have eq9520 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq8607 eq9462
    | exact resolve eq9462 eq8607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8607 eq9462
  have eq9547 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq9520 eq27
    | exact resolve eq27 eq9520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9520
  have eq9669 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq9547
       have r₂ := eq8999
       grind)
    | exact resolve eq9547 eq8999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9547
  have eq9696 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq9669
       grind)
    | exact superpose eq9669 eq22
    | exact resolve eq22 eq9669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9715 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq2501
       have i₂ := eq9669
       grind)
    | exact superpose eq9669 eq2501
    | exact resolve eq2501 eq9669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2501 eq9669
  have eq9720 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq9715
  have eq9721 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq2616 eq9720
    | exact resolve eq9720 eq2616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2616 eq9720
  have eq9722 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq9721
  have eq9728 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq9696
    | exact resolve eq9696 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9696
  have eq11021 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8651 eq8589
    | exact resolve eq8589 eq8651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8651
  have eq11029 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11021
  have eq11035 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11029
    | exact resolve eq11029 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11029
  have eq11036 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq11035
  have eq11135 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11036 eq8589
    | exact resolve eq8589 eq11036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8589
  have eq11139 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq11036
  have eq11142 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq11135
  have eq11244 : (M.op x y) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11142 eq11
    | exact resolve eq11 eq11142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11142
  have eq11252 : (M.op x y) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq11244
  have eq11261 : (M.op x y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11252
       have r₂ := eq11139
       grind)
    | exact resolve eq11252 eq11139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11252
  have eq11292 : (k x x) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11261 eq98
    | exact resolve eq98 eq11261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq11261
  have eq11314 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9034 eq11292
    | exact resolve eq11292 eq9034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9034 eq11292
  have eq17380 : x ≠ y ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq853 x x
       have i₂ := eq2502
       grind)
    | exact superpose eq2502 eq853
    | (have j0 := eq853 x x
       grind)
    | exact resolve eq853 eq2502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853 eq2502
  have eq17382 : x ≠ y ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq17380
  have eq17397 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq17382
       have r₂ := eq9722
       grind)
    | exact resolve eq17382 eq9722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9722 eq17382
  have eq17407 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq9728 eq17397
    | exact resolve eq17397 eq9728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9728 eq17397
  have eq17415 : x = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq8999 eq17407
    | exact resolve eq17407 eq8999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17407
  have eq17451 : x ≠ x ∨ x = (k x x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq17415
       grind)
    | exact superpose eq17415 eq28
    | (have j0 := eq28 x x
       grind)
    | (have r₁ := eq28 x x
       have r₂ := eq17415
       grind)
    | exact resolve eq28 eq17415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq17415
  have eq17462 : x = (k x x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ x) := by grind
  clear eq17451
  have eq17513 : x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq11314
       have i₂ := eq17462
       grind)
    | exact superpose eq17462 eq11314
    | exact resolve eq11314 eq17462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11314 eq17462
  have eq17526 : x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) := by grind
  clear eq17513
  have eq17536 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17526
       have r₂ := eq11139
       grind)
    | exact resolve eq17526 eq11139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11139 eq17526
  have eq17547 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17536 eq27
    | exact resolve eq27 eq17536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17536
  have eq17697 : x = (M.op x y) := by
    first
    | (have r₁ := eq17547
       have r₂ := eq8999
       grind)
    | exact resolve eq17547 eq8999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8999 eq17547
  have eq17718 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq17697
       grind)
    | exact superpose eq17697 eq18
    | exact resolve eq18 eq17697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq17719 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq17697
       grind)
    | exact superpose eq17697 eq22
    | exact resolve eq22 eq17697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq17720 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq17697
       grind)
    | exact superpose eq17697 eq36
    | exact resolve eq36 eq17697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq17721 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq17697
       grind)
    | exact superpose eq17697 eq40
    | exact resolve eq40 eq17697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq17726 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq736
       have i₂ := eq17697
       grind)
    | exact superpose eq17697 eq736
    | exact resolve eq736 eq17697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq17754 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq17719 eq20
    | exact resolve eq20 eq17719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17719
  have eq17938 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq17718 eq734
    | exact resolve eq734 eq17718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17942 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (M.op (M.op x y) (M.op x y))) := by
    intro X1
    first
    | (have i₁ := eq17938 x X1
       have i₂ := eq775 x
       grind)
    | exact superpose eq775 eq17938
    | exact resolve eq17938 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775 eq17938
  have eq17944 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op X1 (M.op (M.op x y) (M.op x y))) := by
    intro X1
    first
    | exact superpose eq17726 eq17942
    | exact resolve eq17942 eq17726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17942
  have eq18631 : ∀ X0 : G, (k X0 (σ (M.op (M.op x y) (M.op x y)))) = X0 := by
    intro X0
    first
    | exact superpose eq17726 eq937
    | exact resolve eq937 eq17726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq18671 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17726 eq2564
    | exact resolve eq2564 eq17726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2564
  have eq18679 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 (M.op (σ x) (M.op (M.op x y) (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq17726 eq734
    | exact resolve eq734 eq17726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq18682 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq17944 eq18679
    | exact resolve eq18679 eq17944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18679
  have eq18690 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq17944 eq18682
    | exact resolve eq18682 eq17944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17944 eq18682
  have eq18807 : (σ (M.op (M.op x y) (M.op x y))) ≠ (σ (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq18631 eq855
    | (have j0 := eq855 (σ (M.op (M.op x y) (M.op x y)))
       grind)
    | (have r₁ := eq855 (σ (M.op (M.op x y) (M.op x y)))
       have r₂ := eq18631 (σ (M.op (M.op x y) (M.op x y)))
       grind)
    | exact resolve eq855 eq18631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855 eq18631
  have eq18844 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by grind
  clear eq18807
  have eq20338 : (M.op (M.op x y) (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2465 eq18690
    | exact resolve eq18690 eq2465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2465 eq18690
  have eq20431 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18671 eq20338
    | exact resolve eq20338 eq18671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20338
  have eq22078 : (M.op (σ x) (σ y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18671 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq18671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18671
  have eq22089 : (M.op (σ x) (σ y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22078
  have eq28563 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq18844 eq693
    | exact resolve eq693 eq18844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq28577 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (σ (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq18844 eq28563
    | exact resolve eq28563 eq18844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18844 eq28563
  have eq28596 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq28577 x x
       have i₂ := eq726 x x
       grind)
    | (have i₁ := eq28577 (σ x) (σ y)
       have i₂ := eq726 x x
       grind)
    | exact superpose eq726 eq28577
    | (have j0 := eq28577 (σ x) (σ y)
       grind)
    | exact resolve eq28577 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726 eq28577
  have eq28611 : (M.op (M.op x y) (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq17726 eq28596
    | exact resolve eq28596 eq17726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28596
  have eq28655 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq28611 eq15
    | exact resolve eq15 eq28611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33800 : (k (σ (M.op x y)) (σ x)) = (σ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22089 eq17721
    | exact resolve eq17721 eq22089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17721 eq22089
  have eq33828 : (k (σ (M.op x y)) (σ x)) = (σ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq33800
    | exact resolve eq33800 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33800
  have eq33839 : (k (σ x) (σ x)) = (σ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17754 eq33828
    | exact resolve eq33828 eq17754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33828
  have eq33847 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6518 eq33839
    | exact resolve eq33839 eq6518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33839
  have eq35924 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33847 eq2545
    | exact resolve eq2545 eq33847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2545 eq33847
  have eq35962 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq35924
  have eq35998 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq35962 eq751
    | exact resolve eq751 eq35962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq36057 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35962 eq17726
    | exact resolve eq17726 eq35962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36059 : (M.op x y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  have eq36066 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq36057
    | exact resolve eq36057 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36057
  have eq36111 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq35998
    | (have j0 := eq35998 X0
       grind)
    | exact resolve eq35998 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35998
  have eq36114 : (σ y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35962 eq36066
    | exact resolve eq36066 eq35962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36066
  have eq36158 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq35962 eq36111
    | exact resolve eq36111 eq35962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35962 eq36111
  have eq37709 : (σ y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36114 eq28655
    | exact resolve eq28655 eq36114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28655 eq36114
  have eq37785 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq37709
    | exact resolve eq37709 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37709
  have eq37876 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37785 eq27
    | exact resolve eq27 eq37785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37785
  have eq38064 : (σ x) = (σ y) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq37876
       have r₂ := eq17754
       grind)
    | exact resolve eq37876 eq17754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37876
  have eq38085 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38064 eq26
    | exact resolve eq26 eq38064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38113 : (σ x) = (k (σ x) (σ x)) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38064 eq2460
    | exact resolve eq2460 eq38064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2460 eq38064
  have eq38703 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38085 eq11
    | exact resolve eq11 eq38085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38085
  have eq38715 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq38703
  have eq38733 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38113 eq38715
    | exact resolve eq38715 eq38113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38113 eq38715
  have eq38734 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq38733
  have eq38767 : (σ (M.op x y)) ≠ (σ x) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38734 eq27
    | exact resolve eq27 eq38734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38734
  have eq38910 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | (have r₁ := eq38767
       have r₂ := eq17754
       grind)
    | exact resolve eq38767 eq17754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38767
  have eq38963 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq38910 eq27
    | exact resolve eq27 eq38910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39034 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq38910 eq6518
    | exact resolve eq6518 eq38910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39048 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq38910 eq17726
    | exact resolve eq17726 eq38910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17726
  have eq39100 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq39034
    | exact resolve eq39034 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39034
  have eq39158 : (M.op x y) ≠ (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq17754 eq38963
    | exact resolve eq38963 eq17754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38963
  have eq39163 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq17754 eq39100
    | exact resolve eq39100 eq17754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39100
  have eq39164 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ y) ∨ y = (σ y) := by grind
  clear eq39163
  have eq39186 : (M.op x y) = (σ y) ∨ y = (σ y) := by
    first
    | (have r₁ := eq39164
       have r₂ := eq39158
       grind)
    | exact resolve eq39164 eq39158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39164
  have eq39198 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq39186 eq26
    | exact resolve eq26 eq39186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39186
  have eq39258 : (M.op x y) = (M.op (σ x) (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq38910 eq39198
    | exact resolve eq39198 eq38910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38910 eq39198
  have eq39392 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq39048 eq39258
    | exact resolve eq39258 eq39048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39048 eq39258
  have eq39412 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (σ y) := by grind
  clear eq39392
  have eq39484 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq39412 eq28611
    | exact resolve eq28611 eq39412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28611 eq39412
  have eq39542 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq39484
    | exact resolve eq39484 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39484
  have eq39586 : (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq17754 eq39542
    | exact resolve eq39542 eq17754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39542
  have eq39617 : y = (σ y) := by
    first
    | (have r₁ := eq39586
       have r₂ := eq39158
       grind)
    | exact resolve eq39586 eq39158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39158 eq39586
  have eq39622 : (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq24
       have i₂ := eq39617
       grind)
    | exact superpose eq39617 eq24
    | exact resolve eq24 eq39617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq39650 : (M.op x y) = (M.op (M.op x y) (σ y)) := by
    first
    | (have i₁ := eq17718
       have i₂ := eq39617
       grind)
    | exact superpose eq39617 eq17718
    | exact resolve eq17718 eq39617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17718
  have eq39671 : (σ y) = (τ (σ y)) := by
    first
    | exact superpose eq39622 eq15
    | exact resolve eq15 eq39622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39622
  have eq53204 : (M.op x y) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36158 eq39650
    | exact resolve eq39650 eq36158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36158
  have eq53229 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq53204
       have r₂ := eq36059
       grind)
    | exact resolve eq53204 eq36059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36059 eq53204
  have eq53264 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53229 eq27
    | exact resolve eq27 eq53229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53229
  have eq53490 : (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq53264
       have r₂ := eq17754
       grind)
    | exact resolve eq53264 eq17754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53264
  have eq53524 : y = (τ (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53490 eq32
    | exact resolve eq32 eq53490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53579 : (M.op x y) = (M.op (M.op x y) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53490 eq39650
    | exact resolve eq39650 eq53490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39650
  have eq53585 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53490 eq39671
    | exact resolve eq39671 eq53490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53490
  have eq53630 : x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq53585
    | exact resolve eq53585 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53585
  have eq53657 : x = y ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq53524
    | exact resolve eq53524 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq53524
  have eq53662 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq53630
       have i₂ := eq17697
       grind)
    | exact superpose eq17697 eq53630
    | exact resolve eq53630 eq17697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53630
  have eq53687 : x = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53657
       have i₂ := eq39617
       grind)
    | exact superpose eq39617 eq53657
    | exact resolve eq53657 eq39617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39617 eq53657
  have eq53707 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq53687
       have i₂ := eq17697
       grind)
    | exact superpose eq17697 eq53687
    | exact resolve eq53687 eq17697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17697 eq53687
  have eq53822 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq53662 eq6518
    | exact resolve eq6518 eq53662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6518
  have eq53909 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ x) := by grind
  clear eq53822
  have eq53992 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq20 eq53909
    | exact resolve eq53909 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53909
  have eq54069 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq17754 eq53992
    | exact resolve eq53992 eq17754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53992
  have eq54070 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ y) := by grind
  clear eq54069
  have eq54122 : (M.op x y) ≠ (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq53707 eq27
    | exact resolve eq27 eq53707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53707
  have eq54447 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq17754 eq54122
    | exact resolve eq54122 eq17754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54122
  have eq54483 : (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq54447
       have r₂ := eq54070
       grind)
    | exact resolve eq54447 eq54070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54070 eq54447
  have eq54506 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq54483 eq26
    | exact resolve eq26 eq54483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq54507 : y = (τ (M.op x y)) := by
    first
    | exact superpose eq54483 eq32
    | exact resolve eq32 eq54483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq54547 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54483 eq20431
    | exact resolve eq20431 eq54483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20431
  have eq54569 : (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq54483 eq39671
    | exact resolve eq39671 eq54483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39671
  have eq54604 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53579 eq54547
    | exact resolve eq54547 eq53579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53579 eq54547
  have eq54605 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq54604
  have eq54630 : y = (M.op x y) := by
    first
    | exact superpose eq54569 eq54507
    | exact resolve eq54507 eq54569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54507 eq54569
  have eq54636 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53662 eq54605
    | exact resolve eq54605 eq53662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53662 eq54605
  have eq54637 : (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq54636
  have eq54686 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (k (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq54630
       grind)
    | exact superpose eq54630 eq37
    | exact resolve eq37 eq54630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq54630
  have eq54738 : ∀ X0 : G, (k (σ x) (σ X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq17720 eq54686
    | exact resolve eq54686 eq17720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17720 eq54686
  have eq54746 : ∀ X0 : G, (k (σ x) (σ X0)) = (k (M.op x y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq54483 eq54738
    | exact resolve eq54738 eq54483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54483 eq54738
  have eq54762 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq54637 eq27
    | exact resolve eq27 eq54637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq54802 : (σ x) = (k (σ x) (σ (σ (σ (σ (σ (M.op (σ x) (M.op x y)))))))) := by
    first
    | exact superpose eq54637 eq1578
    | exact resolve eq1578 eq54637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1578
  have eq54803 : ∀ X0 : G, (k X0 (σ (σ (σ (σ (σ (M.op (σ x) (M.op x y)))))))) = X0 := by
    intro X0
    first
    | exact superpose eq54637 eq1579
    | exact resolve eq1579 eq54637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1579
  have eq54916 : ∀ X0 : G, (k X0 (σ (σ (σ (σ (σ (M.op (σ x) (σ y)))))))) = X0 := by
    intro X0
    first
    | exact superpose eq54506 eq54803
    | exact resolve eq54803 eq54506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54803
  have eq54917 : (σ x) = (k (M.op x y) (σ (σ (σ (σ (σ (M.op (σ x) (M.op x y)))))))) := by
    first
    | exact superpose eq54746 eq54802
    | exact resolve eq54802 eq54746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54746 eq54802
  have eq54956 : (M.op x y) ≠ (σ x) := by
    first
    | exact superpose eq17754 eq54762
    | exact resolve eq54762 eq17754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54762
  have eq54965 : ∀ X0 : G, (k X0 (σ (σ (σ (σ (σ (M.op x y))))))) = X0 := by
    intro X0
    first
    | exact superpose eq54637 eq54916
    | exact resolve eq54916 eq54637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54916
  have eq54966 : (σ x) = (k (M.op x y) (σ (σ (σ (σ (σ (M.op (σ x) (σ y)))))))) := by
    first
    | exact superpose eq54506 eq54917
    | exact resolve eq54917 eq54506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54506 eq54917
  have eq55009 : ∀ X0 : G, (k X0 (σ (σ (σ (σ (σ (M.op x y))))))) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq54965
    | (have j0 := eq54965 X0
       grind)
    | exact resolve eq54965 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54965
  have eq55010 : (σ x) = (k (M.op x y) (σ (σ (σ (σ (σ (M.op x y))))))) := by
    first
    | exact superpose eq54637 eq54966
    | exact resolve eq54966 eq54637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54637 eq54966
  have eq55049 : ∀ X0 : G, (k X0 (σ (σ (σ (σ (σ x)))))) = X0 := by
    intro X0
    first
    | exact superpose eq17754 eq55009
    | exact resolve eq55009 eq17754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55009
  have eq55050 : (σ x) = (k (M.op x y) (σ (σ (σ (σ (σ (M.op x y))))))) := by
    first
    | exact superpose eq20 eq55010
    | exact resolve eq55010 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq55010
  have eq55085 : (σ x) = (k (M.op x y) (σ (σ (σ (σ (σ x)))))) := by
    first
    | exact superpose eq17754 eq55050
    | exact resolve eq55050 eq17754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17754 eq55050
  have eq55102 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq55049 eq55085
    | exact resolve eq55085 eq55049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55049 eq55085
  have eq55115 : False := by grind
  exact eq55115

/-- `Equation4425`: `x ◇ (x ◇ y) = (z ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_y_pxx_pxy_Equation4425 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4425 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4425.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
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
  clear eq36
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
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
  have eq181 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq37 (M.op sF0 sF0)
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq37
    | exact resolve eq37 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : (τ (M.op (σ x) (σ x))) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq90 (M.op sF2 sF2)
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq90
    | exact resolve eq90 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq193 : (τ (M.op (σ y) (σ y))) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq107 (M.op sF3 sF3)
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq107
    | exact resolve eq107 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq560 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq178 X2 X3 X4 (M.op X4 x)
       have i₂ := eq178 X4 x X0 X1
       grind)
    | (have i₁ := eq178 X2 X3 X4 (M.op X4 x)
       have i₂ := eq178 X0 X1 X4 x
       grind)
    | exact superpose eq178 eq178
    | exact resolve eq178 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (M.op X3 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq178 X1 X2 X3 (M.op X3 x)
       have i₂ := eq16 X3 x X0
       grind)
    | exact superpose eq16 eq178
    | exact resolve eq178 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq178
    | (have j0 := eq178 X0 X1 x y
       grind)
    | exact resolve eq178 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq566 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq178
    | (have j0 := eq178 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq178 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X4 X4) X4) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq16 X2 (M.op X2 x) X4
       have i₂ := eq178 X2 x X0 X1
       grind)
    | (have i₁ := eq16 X2 (M.op X2 x) X4
       have i₂ := eq178 X0 X1 X2 x
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq574 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq565 x x
       have i₂ := eq566 x x
       grind)
    | (have i₁ := eq565 (σ x) (σ y)
       have i₂ := eq566 x x
       grind)
    | exact superpose eq566 eq565
    | (have j0 := eq565 (σ x) (σ y)
       have j1 := eq566 x y
       grind)
    | exact resolve eq565 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq578 : ∀ X0 X3 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X3 (M.op (M.op X0 X0) X0)) := by
    intro X0 X3
    first
    | (have i₁ := eq561 X0 x x X3
       have i₂ := eq566 x x
       grind)
    | (have i₁ := eq561 X0 (σ x) (σ y) X3
       have i₂ := eq566 X0 x
       grind)
    | exact superpose eq566 eq561
    | (have j0 := eq561 X0 (σ x) (σ y) X3
       grind)
    | exact resolve eq561 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq579 : ∀ X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq560 x x X2 X3 X4
       have i₂ := eq566 x x
       grind)
    | (have i₁ := eq560 (σ x) (σ y) X2 X3 X4
       have i₂ := eq566 x x
       grind)
    | exact superpose eq566 eq560
    | (have j0 := eq560 (σ x) (σ y) X2 X3 X4
       grind)
    | exact resolve eq560 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq589 : ∀ X4 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X4 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X4
    first
    | (have i₁ := eq579 x x X4
       have i₂ := eq566 x x
       grind)
    | (have i₁ := eq579 (σ x) (σ y) X4
       have i₂ := eq566 x x
       grind)
    | exact superpose eq566 eq579
    | (have j0 := eq579 (σ x) (σ y) X4
       grind)
    | exact resolve eq579 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq612 : ∀ X2 : G, (M.op (M.op X2 X2) X2) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X2
    first
    | (have i₁ := eq16 x x X2
       have i₂ := eq566 x x
       grind)
    | (have i₁ := eq16 (σ x) (σ y) X2
       have i₂ := eq566 x x
       grind)
    | exact superpose eq566 eq16
    | (have j0 := eq16 (σ x) (σ y) X2
       grind)
    | exact resolve eq16 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq631 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq589 eq174
    | exact resolve eq174 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq762 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq764 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq802 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq803 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq804 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq803 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq1028 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq762
       grind)
    | exact superpose eq762 eq40
    | exact resolve eq40 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq1029 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1028
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1028
    | exact resolve eq1028 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1028
  have eq1031 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq1029
    | exact resolve eq1029 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
  have eq1345 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1031 eq764
    | exact resolve eq764 eq1031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031
  have eq1352 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq1345
       have r₂ := eq27
       grind)
    | exact resolve eq1345 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1345
  have eq1357 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1352 eq182
    | exact resolve eq182 eq1352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq1352
  have eq1387 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq1357
    | exact resolve eq1357 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357
  have eq1392 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq1387
       have r₂ := eq13 x y
       grind)
    | exact resolve eq1387 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1387
  have eq1395 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq762
       have i₂ := eq1392
       grind)
    | exact superpose eq1392 eq762
    | exact resolve eq762 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq1396 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq1392
       grind)
    | exact superpose eq1392 eq35
    | exact resolve eq35 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1392
  have eq1398 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1395
  have eq1401 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1396
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1396
    | exact resolve eq1396 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396
  have eq1420 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq566 x x
       have i₂ := eq1398
       grind)
    | exact superpose eq1398 eq566
    | exact resolve eq566 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1421 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq573 x x X1 X0
       have i₂ := eq1398
       grind)
    | exact superpose eq1398 eq573
    | exact resolve eq573 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573 eq1398
  have eq1424 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1421 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1421
    | (have j0 := eq1421 X0 X1
       grind)
    | exact resolve eq1421 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1421
  have eq1425 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1420
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1420
    | exact resolve eq1420 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420
  have eq1435 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq1424 x X1
       have i₂ := eq612 x
       grind)
    | exact superpose eq612 eq1424
    | exact resolve eq1424 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612 eq1424
  have eq1439 : ∀ X1 : G, (M.op x y) = (M.op X1 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq1425 eq1435
    | exact resolve eq1435 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435
  have eq1445 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1401 eq764
    | exact resolve eq764 eq1401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764 eq1401
  have eq1449 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1445
  have eq1512 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1439 eq181
    | exact resolve eq181 eq1439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq1439
  have eq1514 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1512
    | exact resolve eq1512 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1512
  have eq1566 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1449 eq566
    | exact resolve eq566 eq1449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449
  have eq1571 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1566
    | exact resolve eq1566 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1566
  have eq1583 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1425 eq1571
    | exact resolve eq1571 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1571
  have eq1600 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1583 eq631
    | exact resolve eq631 eq1583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1602 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq1604 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1600
    | exact resolve eq1600 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1600
  have eq1608 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1583 eq1604
    | exact resolve eq1604 eq1583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1604
  have eq1622 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1514 eq804
    | (have j0 := eq804 (σ (M.op x y))
       grind)
    | (have r₁ := eq804 (σ (M.op x y))
       have r₂ := eq1514
       grind)
    | exact resolve eq804 eq1514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1514
  have eq1623 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1622
  have eq1645 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1608 eq152
    | exact resolve eq152 eq1608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq1608
  have eq1648 : y = (k y y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq1645
    | exact resolve eq1645 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645
  have eq1757 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1623 eq566
    | exact resolve eq566 eq1623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1761 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1425 eq1757
    | exact resolve eq1757 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425 eq1757
  have eq1786 : y ≠ y ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq804 y
       have i₂ := eq1648
       grind)
    | exact superpose eq1648 eq804
    | (have j0 := eq804 y
       grind)
    | (have r₁ := eq804 y
       have r₂ := eq1648
       grind)
    | exact resolve eq804 eq1648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804 eq1648
  have eq1787 : y = (M.op y y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1786
  have eq1792 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1761 eq1623
    | exact resolve eq1623 eq1761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1623 eq1761
  have eq1812 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq1792
  have eq1839 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1812 eq589
    | exact resolve eq589 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq1844 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq26 eq1839
    | (have j0 := eq1839 X0
       grind)
    | exact resolve eq1839 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1839
  have eq1848 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1812 eq1844
    | exact resolve eq1844 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1844
  have eq1935 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op y y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq578 y X0
       have i₂ := eq1787
       grind)
    | exact superpose eq1787 eq578
    | exact resolve eq578 eq1787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq1948 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op y y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1583 eq1935
    | exact resolve eq1935 eq1583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1935
  have eq1961 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op y y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq1948
    | (have j0 := eq1948 X0
       grind)
    | exact resolve eq1948 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1948
  have eq1972 : ∀ X0 : G, (σ y) = (M.op X0 (M.op y y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1583 eq1961
    | exact resolve eq1961 eq1583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583 eq1961
  have eq1981 : ∀ X0 : G, (σ y) = (M.op X0 y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1787 eq1972
    | exact resolve eq1972 eq1787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1787 eq1972
  have eq2625 : (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1981 x
       grind)
    | (have i₁ := eq18
       have i₂ := eq1981 x
       grind)
    | exact superpose eq1981 eq18
    | (have j1 := eq1981 x
       grind)
    | exact resolve eq18 eq1981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1981
  have eq2630 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2625
       have r₂ := eq1602
       grind)
    | exact resolve eq2625 eq1602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1602 eq2625
  have eq2660 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2630 eq27
    | exact resolve eq27 eq2630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2666 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2630 eq1812
    | exact resolve eq1812 eq2630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1812
  have eq2667 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq2666
  have eq2672 : y = (τ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq2667 eq31
    | exact resolve eq31 eq2667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq2683 : (τ (M.op (M.op x y) (M.op x y))) = (k y (τ (M.op (M.op x y) (M.op x y)))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq2667 eq193
    | exact resolve eq193 eq2667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq2692 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2667 eq1848
    | exact resolve eq1848 eq2667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1848 eq2667
  have eq2693 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq2692 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2692
  have eq2702 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2693 X0
       grind)
    | (have r₁ := eq2693 X0
       have r₂ := eq2660
       grind)
    | exact resolve eq2693 eq2660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2693
  have eq2705 : (τ (M.op (M.op x y) (M.op x y))) = (k y (τ (M.op (M.op x y) (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2683
       have r₂ := eq2660
       grind)
    | exact resolve eq2683 eq2660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2683
  have eq2716 : y = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2672
       have r₂ := eq2660
       grind)
    | exact resolve eq2672 eq2660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2660 eq2672
  have eq2718 : (τ (M.op x y)) = (k y (τ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2702 eq2705
    | exact resolve eq2705 eq2702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2705
  have eq2727 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2716 eq2718
    | exact resolve eq2718 eq2716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2716 eq2718
  have eq2890 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq802 y y
       have i₂ := eq2727
       grind)
    | exact superpose eq2727 eq802
    | (have j0 := eq802 y y
       grind)
    | (have r₁ := eq802 y y
       have r₂ := eq2727
       grind)
    | exact resolve eq802 eq2727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2727
  have eq2891 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq2890
  have eq2892 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq2891
  have eq2930 : (M.op y y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq566 y y
       have i₂ := eq2892
       grind)
    | exact superpose eq2892 eq566
    | exact resolve eq566 eq2892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2938 : (M.op y y) = (M.op (σ x) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2630 eq2930
    | exact resolve eq2930 eq2630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2630 eq2930
  have eq2952 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2702 eq2938
    | exact resolve eq2938 eq2702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2702 eq2938
  have eq3049 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2892
       have i₂ := eq2952
       grind)
    | exact superpose eq2952 eq2892
    | exact resolve eq2892 eq2952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2892 eq2952
  have eq3078 : y = (M.op x y) := by grind
  clear eq3049
  have eq3097 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3078
       grind)
    | exact superpose eq3078 eq18
    | exact resolve eq18 eq3078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq3098 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq3078
       grind)
    | exact superpose eq3078 eq24
    | exact resolve eq24 eq3078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3078
  have eq3104 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3098 eq20
    | exact resolve eq20 eq3098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3098
  have eq3179 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3097 eq574
    | exact resolve eq574 eq3097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq3097
  have eq3200 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3179 eq631
    | exact resolve eq631 eq3179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq3207 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq3179 eq178
    | exact resolve eq178 eq3179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3208 : (M.op x y) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq3179 eq566
    | exact resolve eq566 eq3179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566 eq3179
  have eq3211 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq3208 eq3207
    | exact resolve eq3207 eq3208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3207
  have eq3218 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3200 eq37
    | exact resolve eq37 eq3200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq3200
  have eq3226 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq3218
    | exact resolve eq3218 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3218
  have eq3228 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq3104 eq3226
    | exact resolve eq3226 eq3104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3226
  have eq3328 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3228 eq802
    | (have j0 := eq802 (σ y) (σ y)
       grind)
    | (have r₁ := eq802 (σ y) (σ y)
       have r₂ := eq3228
       grind)
    | exact resolve eq802 eq3228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802 eq3228
  have eq3329 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3328
  have eq3330 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3329
  have eq3358 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ y) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq3330 eq178
    | exact resolve eq178 eq3330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq3364 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq3330 eq3358
    | exact resolve eq3358 eq3330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3330 eq3358
  have eq3376 : (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq3364 x x
       have i₂ := eq3211 x x
       grind)
    | exact superpose eq3211 eq3364
    | exact resolve eq3364 eq3211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3211 eq3364
  have eq3393 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq3376 eq26
    | exact resolve eq26 eq3376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq3431 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3208 eq3393
    | exact resolve eq3393 eq3208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3208 eq3393
  have eq3452 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq3431 eq27
    | exact resolve eq27 eq3431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq3431
  have eq3466 : (M.op x y) ≠ (σ y) := by
    first
    | exact superpose eq3104 eq3452
    | exact resolve eq3452 eq3104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3104 eq3452
  have eq3469 : False := by grind
  exact eq3469

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_x_x_pyx_Equation4430 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4430 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X3) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  clear eq38
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
  have eq175 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
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
  have eq220 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq32 eq209
    | exact resolve eq209 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq399 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq690 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
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
  have eq692 : ∀ X0 X1 X4 X5 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X4 X5) X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq16 x x X4 X5
       have i₂ := eq16 x x X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq694 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq16 X2 X3 (M.op x X5) X5
       have i₂ := eq16 X0 X1 x X5
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) y) := by
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
  have eq696 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq700 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq694 x x X2 X3 X5
       have i₂ := eq696 x x
       grind)
    | exact superpose eq696 eq694
    | exact resolve eq694 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq703 : ∀ X5 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X5
    first
    | (have i₁ := eq700 x x X5
       have i₂ := eq696 x x
       grind)
    | exact superpose eq696 eq700
    | exact resolve eq700 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq704 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq695 X0 (M.op X0 x)
       have i₂ := eq695 X0 x
       grind)
    | exact superpose eq695 eq695
    | exact resolve eq695 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq695 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq695
    | (have j0 := eq695 x y
       grind)
    | exact resolve eq695 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708 : (M.op (M.op x y) y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq695
    | (have j0 := eq695 (σ x) (σ y)
       grind)
    | exact resolve eq695 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq710 : ∀ X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op x y) y) := by
    intro X2 X3
    first
    | (have i₁ := eq16 x x X2 X3
       have i₂ := eq695 x x
       grind)
    | exact superpose eq695 eq16
    | exact resolve eq16 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq712 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op X0 x) X2 X3
       have i₂ := eq695 X0 x
       grind)
    | exact superpose eq695 eq16
    | exact resolve eq16 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq735 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq695 x x
       have i₂ := eq696 x x
       grind)
    | exact superpose eq696 eq695
    | exact resolve eq695 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq774 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (k X0 X1) X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X3 X1 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq783 : (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq789 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq795 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq796 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq795 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq820 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (k X0 X1) X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq774 X0 X1 x x
       have i₂ := eq696 x x
       grind)
    | exact superpose eq696 eq774
    | (have j0 := eq774 X0 X1 x x
       grind)
    | exact resolve eq774 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696 eq774
  have eq831 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op (k X0 X1) X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq735 eq820
    | (have j0 := eq820 X0 X1
       grind)
    | exact resolve eq820 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820
  have eq833 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq735 eq703
    | exact resolve eq703 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq870 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) ∨ (M.op (M.op (M.op x y) y) X0) = X0 ∨ (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | exact superpose eq704 eq11
    | (have j0 := eq11 (M.op (M.op x y) y) X0
       grind)
    | exact resolve eq11 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq875 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | exact superpose eq704 eq28
    | (have j0 := eq28 X0 (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq28 X0 (M.op (M.op x y) y)
       have r₂ := eq704 X0
       grind)
    | exact resolve eq28 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq878 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have j0 := eq875 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875
  have eq881 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) ∨ (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have j0 := eq870 X0
       have j1 := eq28 (M.op (M.op x y) y) X0
       grind)
    | (have r₁ := eq870 x
       have r₂ := eq28 (M.op (M.op x y) y) x
       grind)
    | (have r₁ := eq870 (M.op (M.op x y) y)
       have r₂ := eq28 (M.op (M.op x y) y) (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq870 (M.op X0 (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)))
       have r₂ := eq28 X0 (M.op (M.op (M.op x y) y) (M.op (M.op x y) y))
       grind)
    | exact resolve eq870 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq883 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | (have j0 := eq881 X0
       have j1 := eq13 (M.op (M.op x y) y) X0
       grind)
    | (have r₁ := eq881 x
       have r₂ := eq13 (M.op (M.op x y) y) x
       grind)
    | (have r₁ := eq881 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op (M.op (M.op x y) y) (M.op (M.op x y) y))
       grind)
    | exact resolve eq881 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq886 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq878 eq399
    | exact resolve eq399 eq878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq901 : ∀ X0 : G, (k X0 (τ (M.op (M.op x y) y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq886 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq886
    | exact resolve eq886 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq1224 : (τ (M.op (M.op x y) y)) ≠ (τ (M.op (M.op x y) y)) ∨ (τ (M.op (M.op x y) y)) = (M.op (τ (M.op (M.op x y) y)) (τ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq901 eq796
    | (have j0 := eq796 (τ (M.op (M.op x y) y))
       grind)
    | (have r₁ := eq796 (τ (M.op (M.op x y) y))
       have r₂ := eq901 (τ (M.op (M.op x y) y))
       grind)
    | exact resolve eq796 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq1227 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq796 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq796
    | (have j0 := eq796 (σ X0)
       grind)
    | exact resolve eq796 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1231 : (τ (M.op (M.op x y) y)) = (M.op (τ (M.op (M.op x y) y)) (τ (M.op (M.op x y) y))) := by grind
  clear eq1224
  have eq3661 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq783
       grind)
    | exact superpose eq783 eq40
    | exact resolve eq40 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3662 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3661
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3661
    | exact resolve eq3661 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3661
  have eq3664 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq3662
    | exact resolve eq3662 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3662
  have eq10997 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq831 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq831
    | (have j0 := eq831 (σ X0) (σ X1)
       grind)
    | exact resolve eq831 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11058 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 (k X0 X1)) ∨ (M.op (M.op x y) y) = (k X0 (k X0 X1)) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (k X0 X1)
       have i₂ := eq831 X0 X1
       grind)
    | exact superpose eq831 eq11
    | (have j0 := eq11 X0 (k X0 X1)
       have j1 := eq831 X0 (k X0 X1)
       grind)
    | exact resolve eq11 eq831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq21497 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) y)) = (M.op (τ (M.op (M.op x y) y)) (τ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq1231 eq712
    | exact resolve eq712 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq21505 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) y)) = (τ (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq1231 eq21497
    | exact resolve eq21497 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231 eq21497
  have eq21521 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq704 eq21505
    | exact resolve eq21505 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704 eq21505
  have eq21573 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq21521 eq14
    | exact resolve eq14 eq21521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24220 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3664 eq789
    | exact resolve eq789 eq3664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24229 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq24220
       have r₂ := eq27
       grind)
    | exact resolve eq24220 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24220
  have eq24672 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq24229 eq220
    | exact resolve eq220 eq24229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq24229
  have eq24713 : y = (k y x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq24672
    | exact resolve eq24672 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24672
  have eq24725 : y = (k y x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq28 y x
       grind)
    | (have r₁ := eq24713
       have r₂ := eq28 (σ y) (σ x)
       grind)
    | (have r₁ := eq24713
       have r₂ := eq28 y x
       grind)
    | exact resolve eq24713 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24713
  have eq24729 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq24725
       have r₂ := eq13 y x
       grind)
    | exact resolve eq24725 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24725
  have eq24733 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | exact superpose eq24729 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | (have r₁ := eq28 (σ y) (σ x)
       have r₂ := eq24729
       grind)
    | exact resolve eq28 eq24729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24729
  have eq24753 : (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) := by grind
  clear eq24733
  have eq24792 : (τ (σ y)) = (k (τ (σ y)) x) ∨ y = (k y x) := by
    first
    | exact superpose eq24753 eq142
    | exact resolve eq142 eq24753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq24753
  have eq24797 : y = (k y x) ∨ y = (k y x) := by
    first
    | exact superpose eq32 eq24792
    | exact resolve eq24792 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq24792
  have eq24798 : y = (k y x) := by grind
  clear eq24797
  have eq24809 : x = (M.op y y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq783
       have i₂ := eq24798
       grind)
    | exact superpose eq24798 eq783
    | exact resolve eq783 eq24798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783
  have eq24811 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq24798
       grind)
    | exact superpose eq24798 eq40
    | exact resolve eq40 eq24798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq24798
  have eq24817 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq24811
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24811
    | exact resolve eq24811 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24811
  have eq24828 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24817 eq789
    | exact resolve eq789 eq24817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq24829 : x = (M.op y y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq24817 eq3664
    | exact resolve eq3664 eq24817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3664 eq24817
  have eq25015 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq710 y y
       have i₂ := eq24809
       grind)
    | exact superpose eq24809 eq710
    | exact resolve eq710 eq24809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24809
  have eq25024 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25015
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25015
    | exact resolve eq25015 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25015
  have eq25069 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24828 eq710
    | exact resolve eq710 eq24828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24828
  have eq25078 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq25069
    | exact resolve eq25069 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25069
  have eq25123 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq710 y y
       have i₂ := eq24829
       grind)
    | exact superpose eq24829 eq710
    | exact resolve eq710 eq24829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24829
  have eq25132 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq25123
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25123
    | exact resolve eq25123 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25123
  have eq25173 : ∀ X0 : G, x = (M.op y x) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq25024 eq878
    | exact resolve eq878 eq25024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25252 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25024 eq21573
    | exact resolve eq21573 eq25024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25024
  have eq25285 : x = (M.op y x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq25252
    | exact resolve eq25252 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25252
  have eq25617 : (M.op (M.op x y) y) = (M.op y x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq695 y x
       have i₂ := eq25285
       grind)
    | exact superpose eq25285 eq695
    | exact resolve eq695 eq25285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25644 : x = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25285 eq25617
    | exact resolve eq25617 eq25285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25285 eq25617
  have eq25794 : x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25644 eq21573
    | exact resolve eq21573 eq25644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25800 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq25644 eq690
    | exact resolve eq690 eq25644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25812 : x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25644 eq710
    | exact resolve eq710 eq25644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25824 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25812
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25812
    | exact resolve eq25812 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25812
  have eq25834 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25800 X0 X1 X2
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25800
    | (have j0 := eq25800 X0 X1 X2
       grind)
    | exact resolve eq25800 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25800
  have eq25836 : x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25794
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25794
    | exact resolve eq25794 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25794
  have eq25923 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X2
    first
    | (have i₁ := eq25834 x x X2
       have i₂ := eq710 x x
       grind)
    | (have i₁ := eq25834 x y X2
       have i₂ := eq710 X2 x
       grind)
    | exact superpose eq710 eq25834
    | (have j0 := eq25834 x y X2
       grind)
    | exact resolve eq25834 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25834
  have eq25925 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25824 eq25836
    | exact resolve eq25836 eq25824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25836
  have eq25953 : ∀ X2 : G, x = (M.op X2 (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X2
    first
    | exact superpose eq25644 eq25923
    | exact resolve eq25923 eq25644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25644 eq25923
  have eq25971 : ∀ X2 : G, (M.op x y) = (M.op X2 (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X2
    first
    | exact superpose eq25824 eq25953
    | exact resolve eq25953 eq25824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25953
  have eq26111 : x = (τ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25925 eq30
    | exact resolve eq30 eq25925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25925
  have eq26232 : (M.op x y) = (τ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25824 eq26111
    | exact resolve eq26111 eq25824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25824 eq26111
  have eq26539 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26232 eq14
    | exact resolve eq14 eq26232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26232
  have eq26612 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq26539
    | exact resolve eq26539 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26539
  have eq26613 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq26612
  have eq29519 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ x)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq25078 eq878
    | exact resolve eq878 eq25078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25078
  have eq34289 : ∀ X0 : G, x = (M.op y x) ∨ (k X0 (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq25132 eq878
    | exact resolve eq878 eq25132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878
  have eq34370 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq25132 eq21573
    | exact resolve eq21573 eq25132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25132
  have eq34413 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq34370
    | exact resolve eq34370 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34370
  have eq34463 : x = (M.op (M.op x y) x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26613 eq34413
    | exact resolve eq34413 eq26613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34413
  have eq34477 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op x x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1 X2
    first
    | exact superpose eq34463 eq690
    | exact resolve eq690 eq34463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34480 : (M.op (M.op x y) y) = (M.op (M.op x y) x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq34463 eq695
    | exact resolve eq695 eq34463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34489 : (M.op x x) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq34463 eq710
    | exact resolve eq710 eq34463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34503 : (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26613 eq34489
    | exact resolve eq34489 eq26613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34489
  have eq34511 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26613 eq34480
    | exact resolve eq34480 eq26613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34480
  have eq34514 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (M.op x x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X2
    first
    | (have i₁ := eq34477 x x X2
       have i₂ := eq710 x x
       grind)
    | (have i₁ := eq34477 x y X2
       have i₂ := eq710 X2 x
       grind)
    | exact superpose eq710 eq34477
    | (have j0 := eq34477 x y X2
       grind)
    | exact resolve eq34477 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34477
  have eq34525 : x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq34463 eq34511
    | exact resolve eq34511 eq34463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34463 eq34511
  have eq34528 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op X2 (M.op x x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X2
    first
    | exact superpose eq26613 eq34514
    | exact resolve eq34514 eq26613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34514
  have eq34537 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op X2 (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X2
    first
    | exact superpose eq34503 eq34528
    | exact resolve eq34528 eq34503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34503 eq34528
  have eq34543 : ∀ X2 : G, x = (M.op X2 x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X2
    first
    | exact superpose eq34525 eq34537
    | exact resolve eq34537 eq34525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34537
  have eq34564 : x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq34525
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq34525
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq34525 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34596 : x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq34564
  have eq34671 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq28 X0 x
       have i₂ := eq34543 X0
       grind)
    | exact superpose eq34543 eq28
    | (have j0 := eq28 X0 x
       grind)
    | (have r₁ := eq28 x x
       have r₂ := eq34543 x
       grind)
    | exact resolve eq28 eq34543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34543
  have eq34715 : ∀ X0 : G, (k X0 x) = X0 ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq34671 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34671
  have eq34868 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1227 x
       have i₂ := eq34715 x
       grind)
    | exact superpose eq34715 eq1227
    | (have j0 := eq1227 x
       grind)
    | exact resolve eq1227 eq34715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34923 : (τ (σ (M.op x y))) = (k (M.op x y) (τ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq125 x
       have i₂ := eq34715 sF1
       grind)
    | exact superpose eq34715 eq125
    | exact resolve eq125 eq34715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq34715
  have eq34929 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq34868
  have eq34932 : (M.op x y) = (k (M.op x y) (τ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq34923
    | exact resolve eq34923 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq34923
  have eq34974 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq34929
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq34929
    | exact resolve eq34929 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34929
  have eq35173 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (σ x) (σ x))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1 X2
    first
    | exact superpose eq34974 eq690
    | exact resolve eq690 eq34974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35185 : (M.op (σ x) (σ x)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq34974 eq710
    | exact resolve eq710 eq34974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35197 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26613 eq35185
    | exact resolve eq35185 eq26613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35185
  have eq35209 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (M.op (σ x) (σ x))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X2
    first
    | (have i₁ := eq35173 x x X2
       have i₂ := eq710 x x
       grind)
    | (have i₁ := eq35173 x y X2
       have i₂ := eq710 X2 x
       grind)
    | exact superpose eq710 eq35173
    | (have j0 := eq35173 x y X2
       grind)
    | exact resolve eq35173 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35173
  have eq35212 : x = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq34525 eq35197
    | exact resolve eq35197 eq34525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35197
  have eq35221 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op X2 (M.op (σ x) (σ x))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X2
    first
    | exact superpose eq26613 eq35209
    | exact resolve eq35209 eq26613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35209
  have eq35224 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq34974 eq35212
    | exact resolve eq35212 eq34974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35212
  have eq35232 : ∀ X2 : G, x = (M.op X2 (M.op (σ x) (σ x))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X2
    first
    | exact superpose eq34525 eq35221
    | exact resolve eq35221 eq34525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35221
  have eq35241 : ∀ X2 : G, x = (M.op X2 (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X2
    first
    | exact superpose eq34974 eq35232
    | exact resolve eq35232 eq34974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34974 eq35232
  have eq35246 : ∀ X2 : G, (σ x) = (M.op X2 (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X2
    first
    | exact superpose eq35224 eq35241
    | exact resolve eq35241 eq35224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35241
  have eq35759 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq35246 eq710
    | exact resolve eq710 eq35246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35246
  have eq35774 : (σ x) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26613 eq35759
    | exact resolve eq35759 eq26613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35759
  have eq40672 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op y x) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq695 y x
       have i₂ := eq25173 X0
       grind)
    | exact superpose eq25173 eq695
    | (have j1 := eq25173 X0
       grind)
    | exact resolve eq695 eq25173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40704 : ∀ X0 : G, x = (M.op (M.op x y) y) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq25173 eq40672
    | (have j0 := eq40672 X0
       have j1 := eq25173 X0
       grind)
    | exact resolve eq40672 eq25173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25173 eq40672
  have eq41199 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ y) (σ x)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq695 X0 x
       have i₂ := eq29519 (M.op X0 x)
       grind)
    | exact superpose eq29519 eq695
    | (have j1 := eq29519 X0
       grind)
    | exact resolve eq695 eq29519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41229 : ∀ X0 : G, (σ x) = (M.op (M.op x y) y) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq29519 eq41199
    | (have j0 := eq41199 X0
       have j1 := eq29519 X0
       grind)
    | exact resolve eq41199 eq29519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29519 eq41199
  have eq42106 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op y x) ∨ (k X0 (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq695 y x
       have i₂ := eq34289 X0
       grind)
    | exact superpose eq34289 eq695
    | (have j1 := eq34289 X0
       grind)
    | exact resolve eq695 eq34289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq42136 : ∀ X0 : G, x = (M.op (M.op x y) y) ∨ (k X0 (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq34289 eq42106
    | (have j0 := eq42106 X0
       have j1 := eq34289 X0
       grind)
    | exact resolve eq42106 eq34289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34289 eq42106
  have eq42743 : ∀ X0 X1 : G, x = (k x X0) ∨ (k X1 (M.op x y)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq883 X0
       have i₂ := eq40704 (M.op sF0 y)
       grind)
    | exact superpose eq40704 eq883
    | (have j1 := eq40704 X1
       grind)
    | exact resolve eq883 eq40704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883
  have eq42823 : ∀ X0 : G, x = (σ x) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq21573
       have i₂ := eq40704 (M.op sF0 y)
       grind)
    | exact superpose eq40704 eq21573
    | (have j1 := eq40704 X0
       grind)
    | exact resolve eq21573 eq40704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42839 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op X0 X1) X1) ∨ (k X2 (M.op x y)) = X2 ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq692 X0 X1 x x
       have i₂ := eq40704 (M.op x x)
       grind)
    | exact superpose eq40704 eq692
    | (have j1 := eq40704 X2
       grind)
    | exact resolve eq692 eq40704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq42849 : ∀ X0 : G, x = (M.op x y) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq710 x x
       have i₂ := eq40704 (M.op x x)
       grind)
    | exact superpose eq40704 eq710
    | (have j1 := eq40704 X0
       grind)
    | exact resolve eq710 eq40704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40704
  have eq42867 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq42849 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq42849
    | (have j0 := eq42849 X0
       grind)
    | exact resolve eq42849 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42849
  have eq42875 : ∀ X2 : G, (M.op x y) = (M.op (M.op x y) y) ∨ (k X2 (M.op x y)) = X2 ∨ y = (M.op x y) := by
    intro X2
    first
    | (have i₁ := eq42839 x x X2
       have i₂ := eq710 x x
       grind)
    | (have i₁ := eq42839 x y X2
       have i₂ := eq710 X2 x
       grind)
    | exact superpose eq710 eq42839
    | (have j0 := eq42839 x y X2
       grind)
    | exact resolve eq42839 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42839
  have eq42879 : ∀ X0 : G, x = (σ x) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq42823 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq42823
    | (have j0 := eq42823 X0
       grind)
    | exact resolve eq42823 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42823
  have eq42964 : ∀ X2 : G, (M.op x y) = (M.op (M.op x y) y) ∨ (k X2 (M.op x y)) = X2 ∨ y = (M.op x y) := by
    intro X2
    first
    | (have i₁ := eq42875 X2
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq42875
    | (have j0 := eq42875 X2
       grind)
    | exact resolve eq42875 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42875
  have eq42968 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq42867 eq42879
    | (have j0 := eq42879 X0
       have j1 := eq42867 X0
       grind)
    | exact resolve eq42879 eq42867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42879
  have eq43054 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq42867 eq796
    | (have j0 := eq796 (M.op x y)
       grind)
    | (have r₁ := eq796 (M.op x y)
       have r₂ := eq42867 (M.op x y)
       grind)
    | exact resolve eq796 eq42867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42867
  have eq43117 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq43054
  have eq43263 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq42968 eq796
    | (have j0 := eq796 (M.op x y)
       grind)
    | (have r₁ := eq796 (M.op x y)
       have r₂ := eq42968 (M.op x y)
       grind)
    | exact resolve eq796 eq42968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42968
  have eq43326 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq43263
  have eq43499 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq43117 eq710
    | exact resolve eq710 eq43117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43516 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq43117 eq43499
    | exact resolve eq43499 eq43117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43117 eq43499
  have eq43574 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq43326 eq690
    | exact resolve eq690 eq43326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43586 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq43326 eq710
    | exact resolve eq710 eq43326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43603 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq43326 eq43586
    | exact resolve eq43586 eq43326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43586
  have eq43615 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    intro X2
    first
    | (have i₁ := eq43574 x x X2
       have i₂ := eq710 x x
       grind)
    | (have i₁ := eq43574 x y X2
       have i₂ := eq710 X2 x
       grind)
    | exact superpose eq710 eq43574
    | (have j0 := eq43574 x y X2
       grind)
    | exact resolve eq43574 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43574
  have eq43630 : ∀ X2 : G, (M.op x y) = (M.op X2 (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    intro X2
    first
    | exact superpose eq43603 eq43615
    | exact resolve eq43615 eq43603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43603 eq43615
  have eq43639 : ∀ X2 : G, (M.op x y) = (M.op X2 (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    intro X2
    first
    | exact superpose eq43326 eq43630
    | exact resolve eq43630 eq43326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43630
  have eq48881 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) X0) ∨ (k X1 (M.op (σ x) (σ y))) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq833 X0
       have i₂ := eq41229 (M.op sF0 y)
       grind)
    | exact superpose eq41229 eq833
    | (have j1 := eq41229 X1
       grind)
    | exact resolve eq833 eq41229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48964 : ∀ X0 : G, (σ x) = (τ (σ x)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq21521
       have i₂ := eq41229 (M.op sF0 y)
       grind)
    | exact superpose eq41229 eq21521
    | (have j1 := eq41229 X0
       grind)
    | exact resolve eq21521 eq41229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41229
  have eq49027 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq30 eq48964
    | (have j0 := eq48964 X0
       grind)
    | exact resolve eq48964 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq48964
  have eq49357 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq49027 eq796
    | (have j0 := eq796 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq796 (M.op (σ x) (σ y))
       have r₂ := eq49027 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq796 eq49027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49027
  have eq49408 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq49357
  have eq49528 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq49408 eq710
    | exact resolve eq710 eq49408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49541 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq49408 eq49528
    | exact resolve eq49528 eq49408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49408 eq49528
  have eq51700 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (τ x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq21521
       have i₂ := eq42136 (M.op sF0 y)
       grind)
    | exact superpose eq42136 eq21521
    | (have j1 := eq42136 X0
       grind)
    | exact resolve eq21521 eq42136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21521
  have eq51701 : ∀ X0 : G, x = (σ x) ∨ (k X0 (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq21573
       have i₂ := eq42136 (M.op sF0 y)
       grind)
    | exact superpose eq42136 eq21573
    | (have j1 := eq42136 X0
       grind)
    | exact resolve eq21573 eq42136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21573
  have eq51734 : ∀ X0 : G, x = (M.op x y) ∨ (k X0 (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq710 x x
       have i₂ := eq42136 (M.op x x)
       grind)
    | exact superpose eq42136 eq710
    | (have j1 := eq42136 X0
       grind)
    | exact resolve eq710 eq42136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42136
  have eq51757 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq51734 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq51734
    | (have j0 := eq51734 X0
       grind)
    | exact resolve eq51734 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51734
  have eq51770 : ∀ X0 : G, x = (σ x) ∨ (k X0 (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq51701 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq51701
    | (have j0 := eq51701 X0
       grind)
    | exact resolve eq51701 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51701
  have eq51861 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (M.op x y) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq51757 eq51770
    | (have j0 := eq51770 X0
       have j1 := eq51757 X0
       grind)
    | exact resolve eq51770 eq51757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51770
  have eq51954 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq51757 eq796
    | (have j0 := eq796 (M.op x y)
       grind)
    | (have r₁ := eq796 (M.op x y)
       have r₂ := eq51757 (M.op x y)
       grind)
    | exact resolve eq796 eq51757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51757
  have eq52015 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq51954
  have eq52132 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq51861 eq796
    | (have j0 := eq796 (M.op x y)
       grind)
    | (have r₁ := eq796 (M.op x y)
       have r₂ := eq51861 (M.op x y)
       grind)
    | exact resolve eq796 eq51861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51861
  have eq52193 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq52132
  have eq53876 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq52193 eq35774
    | exact resolve eq35774 eq52193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35774 eq52193
  have eq53909 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) := by grind
  clear eq53876
  have eq57586 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (τ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq51700 eq796
    | (have j0 := eq796 (M.op x y)
       grind)
    | (have r₁ := eq796 (M.op x y)
       have r₂ := eq51700 (M.op x y)
       grind)
    | exact resolve eq796 eq51700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51700
  have eq57648 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (τ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq57586
  have eq57705 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (τ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq52015 eq57648
    | exact resolve eq57648 eq52015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57648
  have eq58886 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (k (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (τ x) = (M.op (M.op x y) (τ x)) ∨ (M.op (M.op x y) (M.op x y)) = (τ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq34932 eq11058
    | (have j0 := eq11058 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq11058 eq34932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34932
  have eq59136 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (k (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ (τ x) = (M.op (M.op x y) (τ x)) ∨ (M.op (M.op x y) (M.op x y)) = (τ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq58886
  have eq59338 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) y) ∨ (τ x) = (M.op (M.op x y) (τ x)) ∨ (M.op (M.op x y) (M.op x y)) = (τ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq34596 eq59136
    | exact resolve eq59136 eq34596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34596 eq59136
  have eq59472 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ (τ x) = (M.op (M.op x y) (τ x)) ∨ (M.op (M.op x y) (M.op x y)) = (τ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq52015 eq59338
    | exact resolve eq59338 eq52015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59338
  have eq59538 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ (τ (M.op x y)) = (M.op (M.op x y) (τ (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = (τ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq52015 eq59472
    | exact resolve eq59472 eq52015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59472
  have eq59588 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ (τ (M.op x y)) = (M.op (M.op x y) (τ (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = (τ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq52015 eq59538
    | exact resolve eq59538 eq52015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52015 eq59538
  have eq59624 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op (M.op x y) (M.op x y)) = (τ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq57705 eq59588
    | exact resolve eq59588 eq57705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59588
  have eq59625 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ (M.op (M.op x y) (M.op x y)) = (τ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq59624
  have eq59651 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq57705 eq59625
    | exact resolve eq59625 eq57705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57705 eq59625
  have eq59652 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq59651
  have eq59669 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq25971 eq59652
    | (have j1 := eq25971 (M.op x y)
       grind)
    | exact resolve eq59652 eq25971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25971 eq59652
  have eq59670 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq59669
  have eq59698 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq59670 eq28
    | (have j0 := eq28 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq28 (M.op x y) (M.op x y)
       have r₂ := eq59670
       grind)
    | exact resolve eq28 eq59670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59670
  have eq59723 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq59698
  have eq59767 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq59723 eq1227
    | (have j0 := eq1227 (M.op x y)
       grind)
    | exact resolve eq1227 eq59723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59723
  have eq59784 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq59767
  have eq59788 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq59784
    | exact resolve eq59784 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59784
  have eq59851 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq59788 eq710
    | exact resolve eq710 eq59788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59869 : (M.op (M.op x y) (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26613 eq59851
    | exact resolve eq59851 eq26613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59851
  have eq59887 : x = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq34525 eq59869
    | exact resolve eq59869 eq34525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34525 eq59869
  have eq59899 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq35224 eq59887
    | exact resolve eq59887 eq35224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35224 eq59887
  have eq59910 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq53909 eq59899
    | exact resolve eq59899 eq53909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53909 eq59899
  have eq60018 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq59910 eq59788
    | exact resolve eq59788 eq59910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59788 eq59910
  have eq60055 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq60018
  have eq60148 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq60055
  have eq65964 : x ≠ x ∨ x = (k x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq42743 (M.op x y) x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42743
  have eq65965 : x = (k x (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq65964
  have eq66061 : (M.op (σ x) (σ x)) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq65965 eq10997
    | (have j0 := eq10997 x (M.op x y)
       grind)
    | exact resolve eq10997 eq65965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10997
  have eq66062 : x = (M.op x x) ∨ (k x x) = (M.op (M.op x y) y) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq65965 eq11058
    | (have j0 := eq11058 x x
       grind)
    | exact resolve eq11058 eq65965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11058 eq65965
  have eq66065 : x = (M.op x x) ∨ (k x x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq66062
  have eq66069 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x x) ∨ (k x x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq707 eq66065
    | exact resolve eq66065 eq707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66065
  have eq66070 : (M.op (σ x) (σ x)) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq66061
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq66061
    | exact resolve eq66061 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66061
  have eq66082 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (k x x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq43516 eq66069
    | exact resolve eq66069 eq43516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66069
  have eq66083 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ x) (σ x)) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq66070
    | exact resolve eq66070 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66070
  have eq66094 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (k (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq43516 eq66082
    | exact resolve eq66082 eq43516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66082
  have eq66095 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ x) (σ x)) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq66083
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq66083
    | exact resolve eq66083 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66083
  have eq66102 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq42964 eq66094
    | exact resolve eq66094 eq42964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42964 eq66094
  have eq66103 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq66102
  have eq66104 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ x) (σ x)) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq66095
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq66095
    | exact resolve eq66095 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq66095
  have eq66106 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq43516 eq66103
    | exact resolve eq66103 eq43516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43516 eq66103
  have eq66107 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq66106
  have eq66108 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ x) (σ x)) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq66104
    | exact resolve eq66104 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66104
  have eq66110 : (M.op x y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ x) (σ x)) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26613 eq66108
    | exact resolve eq66108 eq26613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66108
  have eq66112 : (M.op x y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (M.op x y)) ∨ (M.op (σ x) (σ x)) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26613 eq66110
    | exact resolve eq66110 eq26613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66110
  have eq66114 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (M.op x y)) ∨ (M.op (σ x) (σ x)) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq43639 eq66112
    | (have j1 := eq43639 (M.op x y)
       grind)
    | exact resolve eq66112 eq43639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43639 eq66112
  have eq66116 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op (σ x) (σ x)) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq43326 eq66114
    | exact resolve eq66114 eq43326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66114
  have eq66117 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op (σ x) (σ x)) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by grind
  clear eq66116
  have eq66119 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq43326 eq66117
    | exact resolve eq66117 eq43326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43326 eq66117
  have eq66122 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq66107 eq66119
    | exact resolve eq66119 eq66107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66107 eq66119
  have eq66123 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq66122
  have eq66211 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq66123 eq710
    | exact resolve eq710 eq66123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66229 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq66123 eq66211
    | exact resolve eq66211 eq66123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66123 eq66211
  have eq66361 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq66229 eq833
    | exact resolve eq833 eq66229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833
  have eq66455 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq66229 eq49541
    | exact resolve eq49541 eq66229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49541
  have eq69419 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq66455 eq708
    | exact resolve eq708 eq66455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69428 : (M.op x y) ≠ (σ y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq69437 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq69419
    | exact resolve eq69419 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69419
  have eq69441 : (σ y) = (M.op (M.op x y) y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq66455 eq69437
    | exact resolve eq69437 eq66455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66455 eq69437
  have eq69443 : (M.op x y) = (σ y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq66229 eq69441
    | exact resolve eq69441 eq66229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69441
  have eq69444 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq69443
       have r₂ := eq69428
       grind)
    | exact resolve eq69443 eq69428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69428 eq69443
  have eq69446 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq69444 eq27
    | exact resolve eq27 eq69444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69444
  have eq69504 : y = (M.op x y) ∨ x = (σ x) := by
    first
    | (have r₁ := eq69446
       have r₂ := eq26613
       grind)
    | exact resolve eq69446 eq26613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69446
  have eq69512 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq69504
       grind)
    | exact superpose eq69504 eq18
    | exact resolve eq18 eq69504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69513 : (σ (M.op x y)) = (σ y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq24
       have i₂ := eq69504
       grind)
    | exact superpose eq69504 eq24
    | exact resolve eq24 eq69504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69770 : (σ (M.op x y)) = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq20 eq69513
    | exact resolve eq69513 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69513
  have eq69771 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (σ x) := by
    first
    | exact superpose eq707 eq69512
    | exact resolve eq69512 eq707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69512
  have eq69838 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq69504 eq69771
    | exact resolve eq69771 eq69504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69771
  have eq70215 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq69838 eq28
    | (have j0 := eq28 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq28 (M.op x y) (M.op x y)
       have r₂ := eq69838
       grind)
    | exact resolve eq28 eq69838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70239 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (σ x) := by grind
  clear eq70215
  have eq70314 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (σ x) := by
    first
    | exact superpose eq70239 eq1227
    | (have j0 := eq1227 (M.op x y)
       grind)
    | exact resolve eq1227 eq70239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70239
  have eq70331 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (σ x) := by grind
  clear eq70314
  have eq70333 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (σ x) := by
    first
    | exact superpose eq20 eq70331
    | exact resolve eq70331 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70331
  have eq70340 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq69770 eq70333
    | exact resolve eq70333 eq69770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69770 eq70333
  have eq70399 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (σ y) (σ y))) ∨ x = (σ x) := by
    intro X0 X1 X2
    first
    | exact superpose eq70340 eq690
    | exact resolve eq690 eq70340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70411 : (M.op (σ y) (σ y)) = (M.op (M.op x y) y) ∨ x = (σ x) := by
    first
    | exact superpose eq70340 eq710
    | exact resolve eq710 eq70340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70427 : (M.op (M.op x y) (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq69504 eq70411
    | exact resolve eq70411 eq69504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70411
  have eq70439 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (M.op (σ y) (σ y))) ∨ x = (σ x) := by
    intro X2
    first
    | (have i₁ := eq70399 x x X2
       have i₂ := eq710 x x
       grind)
    | (have i₁ := eq70399 x y X2
       have i₂ := eq710 X2 x
       grind)
    | exact superpose eq710 eq70399
    | (have j0 := eq70399 x y X2
       grind)
    | exact resolve eq70399 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70399
  have eq70446 : (M.op x y) = (M.op (σ y) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq69838 eq70427
    | exact resolve eq70427 eq69838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70427
  have eq70455 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op X2 (M.op (σ y) (σ y))) ∨ x = (σ x) := by
    intro X2
    first
    | exact superpose eq69504 eq70439
    | exact resolve eq70439 eq69504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70439
  have eq70468 : ∀ X2 : G, (M.op x y) = (M.op X2 (M.op (σ y) (σ y))) ∨ x = (σ x) := by
    intro X2
    first
    | exact superpose eq69838 eq70455
    | exact resolve eq70455 eq69838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70455
  have eq70475 : ∀ X2 : G, (M.op x y) = (M.op X2 (σ y)) ∨ x = (σ x) := by
    intro X2
    first
    | exact superpose eq70340 eq70468
    | exact resolve eq70468 eq70340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70468
  have eq70481 : (M.op x y) = (σ y) ∨ x = (σ x) ∨ x = (σ x) := by
    first
    | exact superpose eq70446 eq70340
    | exact resolve eq70340 eq70446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70340
  have eq70491 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (M.op x y) (σ y))) ∨ x = (σ x) := by
    intro X0 X1 X2
    first
    | exact superpose eq70446 eq690
    | exact resolve eq690 eq70446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690 eq70446
  have eq70514 : (M.op x y) = (σ y) ∨ x = (σ x) := by grind
  clear eq70481
  have eq70532 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (M.op (M.op x y) (σ y))) ∨ x = (σ x) := by
    intro X2
    first
    | (have i₁ := eq70491 x x X2
       have i₂ := eq710 x x
       grind)
    | (have i₁ := eq70491 x y X2
       have i₂ := eq710 X2 x
       grind)
    | exact superpose eq710 eq70491
    | (have j0 := eq70491 x y X2
       grind)
    | exact resolve eq70491 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70491
  have eq70548 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op X2 (M.op (M.op x y) (σ y))) ∨ x = (σ x) := by
    intro X2
    first
    | exact superpose eq69504 eq70532
    | exact resolve eq70532 eq69504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69504 eq70532
  have eq70561 : ∀ X2 : G, (M.op x y) = (M.op X2 (M.op (M.op x y) (σ y))) ∨ x = (σ x) := by
    intro X2
    first
    | exact superpose eq69838 eq70548
    | exact resolve eq70548 eq69838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69838 eq70548
  have eq70570 : ∀ X2 : G, (M.op x y) = (M.op X2 (M.op x y)) ∨ x = (σ x) := by
    intro X2
    first
    | exact superpose eq70475 eq70561
    | exact resolve eq70561 eq70475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70475 eq70561
  have eq70577 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq70514 eq26
    | exact resolve eq26 eq70514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70681 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq70514 eq60148
    | (have r₁ := eq60148
       have r₂ := eq70514
       grind)
    | exact resolve eq60148 eq70514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70514
  have eq70692 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by grind
  clear eq70681
  have eq70771 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq70570 eq70577
    | exact resolve eq70577 eq70570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70570 eq70577
  have eq71092 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq70771 eq27
    | exact resolve eq27 eq70771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70771
  have eq71145 : x = (σ x) := by
    first
    | (have r₁ := eq71092
       have r₂ := eq70692
       grind)
    | exact resolve eq71092 eq70692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70692 eq71092
  have eq71152 : (M.op x y) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq71145
       grind)
    | exact superpose eq71145 eq18
    | exact resolve eq18 eq71145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq71175 : (M.op (M.op x y) y) = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq707
       have i₂ := eq71145
       grind)
    | exact superpose eq71145 eq707
    | exact resolve eq707 eq71145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707 eq71145
  have eq95412 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq48881 X0 (M.op sF2 sF3)
       grind)
    | exact superpose eq48881 eq26
    | (have j1 := eq48881 (σ y) X0
       grind)
    | exact resolve eq26 eq48881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48881
  have eq95561 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq95412 eq796
    | (have j0 := eq796 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq796 (M.op (σ x) (σ y))
       have r₂ := eq95412 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq796 eq95412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796 eq95412
  have eq95624 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq95561
  have eq95775 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq95624 eq710
    | exact resolve eq710 eq95624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95794 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq95624 eq95775
    | exact resolve eq95775 eq95624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95624 eq95775
  have eq95978 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq95794 eq66361
    | exact resolve eq66361 eq95794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66361 eq95794
  have eq99505 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq95978 eq708
    | exact resolve eq708 eq95978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708 eq95978
  have eq99528 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq99505
    | exact resolve eq99505 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99505
  have eq99532 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq66229 eq99528
    | exact resolve eq99528 eq66229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99528
  have eq99533 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq99532
  have eq99544 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq99533 eq735
    | exact resolve eq735 eq99533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735 eq99533
  have eq99600 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq99544
    | exact resolve eq99544 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99544
  have eq99611 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq66229 eq99600
    | exact resolve eq99600 eq66229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66229 eq99600
  have eq99612 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq99611
  have eq99622 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq99612 eq27
    | exact resolve eq27 eq99612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99612
  have eq99688 : y = (M.op x y) := by
    first
    | (have r₁ := eq99622
       have r₂ := eq26613
       grind)
    | exact resolve eq99622 eq26613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26613 eq99622
  have eq99696 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq99688
       grind)
    | exact superpose eq99688 eq24
    | exact resolve eq24 eq99688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq99851 : (M.op x y) = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq71152
       have i₂ := eq99688
       grind)
    | exact superpose eq99688 eq71152
    | exact resolve eq71152 eq99688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71152
  have eq100180 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq99696 eq20
    | exact resolve eq20 eq99696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99696
  have eq100906 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq99851 eq71175
    | exact resolve eq71175 eq99851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71175
  have eq100958 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq100906
       have i₂ := eq99688
       grind)
    | exact superpose eq99688 eq100906
    | exact resolve eq100906 eq99688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100906
  have eq101034 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq100958 eq28
    | (have j0 := eq28 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq28 (M.op x y) (M.op x y)
       have r₂ := eq100958
       grind)
    | exact resolve eq28 eq100958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq101061 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq101034
  have eq101149 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq101061 eq1227
    | (have j0 := eq1227 (M.op x y)
       grind)
    | exact resolve eq1227 eq101061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227 eq101061
  have eq101166 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq101149
  have eq101168 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq101166
    | exact resolve eq101166 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq101166
  have eq101175 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq100180 eq101168
    | exact resolve eq101168 eq100180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100180 eq101168
  have eq101263 : (M.op (σ y) (σ y)) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq101175 eq710
    | exact resolve eq710 eq101175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq101282 : (M.op (M.op x y) (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq101263
       have i₂ := eq99688
       grind)
    | exact superpose eq99688 eq101263
    | exact resolve eq101263 eq99688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99688 eq101263
  have eq101301 : (σ y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq101175 eq101282
    | exact resolve eq101282 eq101175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101175 eq101282
  have eq101313 : (M.op x y) = (σ y) := by
    first
    | exact superpose eq100958 eq101301
    | exact resolve eq101301 eq100958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100958 eq101301
  have eq101339 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq101313 eq26
    | exact resolve eq26 eq101313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq101446 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq101313 eq60148
    | (have r₁ := eq60148
       have r₂ := eq101313
       grind)
    | exact resolve eq60148 eq101313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60148 eq101313
  have eq101495 : (M.op x y) = (σ (M.op x y)) := by grind
  clear eq101446
  have eq101589 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq99851 eq101339
    | exact resolve eq101339 eq99851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99851 eq101339
  have eq101987 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq101589 eq27
    | exact resolve eq27 eq101589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq101589
  have eq102046 : False := by grind
  exact eq102046

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_x_pyx_x_pyx_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq293 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ y) (σ x)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
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
  have eq309 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq303 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq310 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq309 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq317 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq310 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq310 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq310 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq327 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq293
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq293 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq331 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq327
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq327
    | exact resolve eq327 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq451 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq317 X1 (τ X0)
       grind)
    | exact superpose eq317 eq18
    | (have j1 := eq317 X1 (τ X0)
       grind)
    | exact resolve eq18 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq468 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq317 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq896 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq451 X1 (τ X0)
       grind)
    | exact superpose eq451 eq17
    | (have j1 := eq451 X1 (τ X0)
       grind)
    | exact resolve eq17 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq451
  have eq901 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq896 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq896
    | (have j0 := eq896 X0 X1
       grind)
    | exact resolve eq896 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq915 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq901 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq901
    | (have j0 := eq901 X0 X1
       grind)
    | exact resolve eq901 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq918 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq915 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq915
    | (have j0 := eq915 X0 X1
       grind)
    | exact resolve eq915 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915
  have eq978 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq918 X0 X1
       have i₂ := eq317 X0 X1
       grind)
    | exact superpose eq317 eq918
    | (have j0 := eq918 X1 X0
       have j1 := eq317 X1 X0
       grind)
    | exact resolve eq918 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317 eq918
  have eq1045 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq978 X0 X1
       have j1 := eq468 X1 X0
       grind)
    | (have r₁ := eq978 X1 X0
       have r₂ := eq468 X0 X1
       grind)
    | exact resolve eq978 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468 eq978
  have eq1098 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq1045 X1 (σ X0)
       grind)
    | exact superpose eq1045 eq28
    | (have j1 := eq1045 X1 (σ X0)
       grind)
    | exact resolve eq28 eq1045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1045
  have eq1116 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1098 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1098
    | (have j0 := eq1098 X0 X1
       grind)
    | exact resolve eq1098 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098
  have eq1146 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1116 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1116
    | (have j0 := eq1116 X0 X1
       grind)
    | exact resolve eq1116 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq1929 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1146 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1146
    | exact resolve eq1146 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146
  have eq2008 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1929 x y
       grind)
    | exact superpose eq1929 eq16
    | (have j1 := eq1929 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1929 x y
       grind)
    | exact resolve eq16 eq1929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1929
  have eq2041 : y = (k y x) := by grind
  clear eq2008
  have eq2328 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq331
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq331
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq331 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2329 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op y x) ∨ (M.op x y) = (k y x) := by grind
  clear eq2328
  have eq2330 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq2329
       have r₂ := eq12 y x
       grind)
    | exact resolve eq2329 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2329
  have eq2331 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq2330
       have i₂ := eq2041
       grind)
    | exact superpose eq2041 eq2330
    | exact resolve eq2330 eq2041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2330
  have eq2332 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2331
       have i₂ := eq2041
       grind)
    | exact superpose eq2041 eq2331
    | exact resolve eq2331 eq2041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2331
  have eq2333 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq331
       have i₂ := eq2332
       grind)
    | exact superpose eq2332 eq331
    | exact resolve eq331 eq2332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331 eq2332
  have eq2342 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2333
  have eq2343 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2342
       have i₂ := eq2041
       grind)
    | exact superpose eq2041 eq2342
    | exact resolve eq2342 eq2041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2342
  have eq2344 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2343
  have eq2346 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2344
       grind)
    | exact superpose eq2344 eq16
    | exact resolve eq16 eq2344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2344
  have eq2364 : (σ y) ≠ (σ y) ∨ y = (M.op y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq2346
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq2346
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq2346 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2365 : y = (M.op y x) ∨ (M.op x y) = (k y x) := by grind
  clear eq2364
  have eq2367 : (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq2365
       have r₂ := eq12 y x
       grind)
    | exact resolve eq2365 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2365
  have eq2368 : y = (M.op x y) := by
    first
    | (have i₁ := eq2367
       have i₂ := eq2041
       grind)
    | exact superpose eq2041 eq2367
    | exact resolve eq2367 eq2041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2041 eq2367
  have eq2369 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2346
       have i₂ := eq2368
       grind)
    | exact superpose eq2368 eq2346
    | exact resolve eq2346 eq2368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2346 eq2368
  have eq2380 : False := by grind
  exact eq2380

/-- `Equation4480`: `x ◇ (y ◇ y) = (y ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_y_pxy_Equation4480 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4480 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4480.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X0) X1) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq22 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq43 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq34 (τ X0)
       grind)
    | exact superpose eq34 eq19
    | exact resolve eq19 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq74 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq107 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq71 x y
       grind)
    | exact superpose eq71 eq16
    | (have j1 := eq71 x y
       grind)
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq34 (σ x)
       have i₂ := eq71 x x
       grind)
    | exact superpose eq71 eq34
    | (have j1 := eq71 X0 X0
       grind)
    | exact resolve eq34 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq117 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq112 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq120 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq117 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq117
    | (have j0 := eq117 X0
       grind)
    | exact resolve eq117 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq266 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq74
    | exact resolve eq74 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq290 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq266 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq266
    | (have j0 := eq266 X0 X1
       grind)
    | exact resolve eq266 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq730 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k (τ X0) (k (τ X0) (τ X0)))) = (M.op X0 (σ (k (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq120 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq120
    | exact resolve eq120 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq747 : ∀ X0 : G, (σ (k (τ X0) (k (τ X0) (τ X0)))) = (M.op X0 (k X0 (σ (τ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq730 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq730
    | (have j0 := eq730 X0
       grind)
    | exact resolve eq730 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq748 : ∀ X0 : G, (σ (k (τ X0) (k (τ X0) (τ X0)))) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq747 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq747
    | (have j0 := eq747 X0
       grind)
    | exact resolve eq747 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq749 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq748 X0
       have i₂ := eq19 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq19 eq748
    | (have j0 := eq748 X0
       grind)
    | exact resolve eq748 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq750 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k X0 (k X0 (σ (τ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq749 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq749
    | (have j0 := eq749 X0
       grind)
    | exact resolve eq749 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq751 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq750 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq750
    | (have j0 := eq750 X0
       grind)
    | exact resolve eq750 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq895 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq751 X0
       grind)
    | exact superpose eq751 eq34
    | (have j1 := eq751 X0
       grind)
    | exact resolve eq34 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq751
  have eq1084 : ∀ X0 : G, (k X0 (σ (k (τ X0) (τ X0)))) = (σ (M.op (τ X0) (k (τ X0) (τ X0)))) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq895 (τ X0)
       grind)
    | exact superpose eq895 eq19
    | (have j1 := eq895 (τ X0)
       grind)
    | exact resolve eq19 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq895
  have eq1087 : ∀ X0 : G, (k X0 (σ (τ (k X0 X0)))) = (σ (M.op (τ X0) (τ (k X0 X0)))) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1084 X0
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq1084
    | (have j0 := eq1084 X0
       grind)
    | exact resolve eq1084 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1107 : ∀ X0 : G, (k X0 (k X0 X0)) = (σ (M.op (τ X0) (τ (k X0 X0)))) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1087 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq1087
    | (have j0 := eq1087 X0
       grind)
    | exact resolve eq1087 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq1125 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X0 (k X0 X0)) = (σ (M.op (τ X0) (τ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1107 X0
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq1107
    | (have j0 := eq1107 X0
       grind)
    | exact resolve eq1107 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq1258 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq290 (τ X1) (τ X0)
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq290
    | (have j0 := eq290 (τ X1) (τ X0)
       grind)
    | exact resolve eq290 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq290
  have eq1324 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X1) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1258 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1258
    | (have j0 := eq1258 X0 X1
       grind)
    | exact resolve eq1258 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258
  have eq133017 : ∀ X0 : G, (k X0 (σ (τ (k X0 X0)))) = (σ (M.op (τ X0) (τ (k X0 X0)))) ∨ (k X0 (k X0 X0)) = (σ (M.op (τ X0) (τ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq43 X0
       have i₂ := eq1125 X0
       grind)
    | exact superpose eq1125 eq43
    | (have j1 := eq1125 X0
       grind)
    | exact resolve eq43 eq1125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125
  have eq133331 : ∀ X0 : G, (k X0 (k X0 X0)) = (σ (M.op (τ X0) (τ (k X0 X0)))) ∨ (k X0 (k X0 X0)) = (σ (M.op (τ X0) (τ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq133017 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq133017
    | (have j0 := eq133017 X0
       grind)
    | exact resolve eq133017 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133017
  have eq133332 : ∀ X0 : G, (k X0 (k X0 X0)) = (σ (M.op (τ X0) (τ (k X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq133331 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133331
  have eq133630 : ∀ X0 : G, (k (σ X0) (k (σ X0) (σ X0))) = (σ (M.op (τ (σ X0)) (k X0 (τ (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq133332 (σ X0)
       have i₂ := eq31 X0 (σ X0)
       grind)
    | exact superpose eq31 eq133332
    | exact resolve eq133332 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq133332
  have eq134040 : ∀ X0 : G, (k (σ X0) (k (σ X0) (σ X0))) = (σ (M.op X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq133630 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq133630
    | exact resolve eq133630 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133630
  have eq134058 : ∀ X0 : G, (σ (k X0 (k (τ (σ X0)) X0))) = (σ (M.op X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq134040 X0
       have i₂ := eq22 (σ X0) X0 X0
       grind)
    | exact superpose eq22 eq134040
    | exact resolve eq134040 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq134040
  have eq134072 : ∀ X0 : G, (σ (k X0 (k X0 X0))) = (σ (M.op X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq134058 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq134058
    | exact resolve eq134058 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134058
  have eq135060 : ∀ X0 : G, (k X0 (k X0 X0)) = (τ (σ (M.op X0 (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 (k X0 X0))
       have i₂ := eq134072 X0
       grind)
    | exact superpose eq134072 eq10
    | exact resolve eq10 eq134072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135507 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq135060 X0
       have i₂ := eq10 (M.op X0 (k X0 X0))
       grind)
    | exact superpose eq10 eq135060
    | exact resolve eq135060 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135060
  have eq135735 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq135507 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq135507
    | exact resolve eq135507 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135507
  have eq136158 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq135735 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq135735
    | exact resolve eq135735 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135735
  have eq136318 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (M.op X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq136158 X0
       have i₂ := eq134072 X0
       grind)
    | exact superpose eq134072 eq136158
    | exact resolve eq136158 eq134072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134072 eq136158
  have eq168531 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq1324 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168532 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq168531 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168531
  have eq169104 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq43 X0
       have i₂ := eq168532 X0
       grind)
    | exact superpose eq168532 eq43
    | (have j1 := eq168532 X0
       grind)
    | exact resolve eq43 eq168532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq168532
  have eq169217 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq169104 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq169104
    | (have j0 := eq169104 X0
       grind)
    | exact resolve eq169104 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169104
  have eq169218 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq169217 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169217
  have eq170265 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq169218 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq169218
    | exact resolve eq169218 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170300 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X1) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq169218 X1
       have i₂ := eq1324 X0 X1
       grind)
    | exact superpose eq1324 eq169218
    | (have j1 := eq1324 X0 X1
       grind)
    | exact resolve eq169218 eq1324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324
  have eq170354 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq169218 X0
       grind)
    | exact superpose eq169218 eq10
    | exact resolve eq10 eq169218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169218
  have eq170866 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq170300 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq170300
    | (have j0 := eq170300 X0 X1
       grind)
    | exact resolve eq170300 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170300
  have eq170885 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq170265 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq170265
    | exact resolve eq170265 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170265
  have eq171196 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq170885 X0
       grind)
    | exact superpose eq170885 eq10
    | exact resolve eq10 eq170885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171761 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq171196 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq171196
    | exact resolve eq171196 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171196
  have eq172269 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq136318 X0
       have i₂ := eq171761 X0
       grind)
    | exact superpose eq171761 eq136318
    | exact resolve eq136318 eq171761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136318
  have eq172498 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq171761 (σ X0)
       grind)
    | exact superpose eq171761 eq15
    | exact resolve eq15 eq171761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172867 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq172498 X0
       have i₂ := eq170885 X0
       grind)
    | exact superpose eq170885 eq172498
    | exact resolve eq172498 eq170885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170885 eq172498
  have eq173805 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq170354 X0
       have i₂ := eq171761 X0
       grind)
    | exact superpose eq171761 eq170354
    | exact resolve eq170354 eq171761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170354
  have eq173818 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq173805 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq173805
    | exact resolve eq173805 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175816 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq172867 X0
       grind)
    | exact superpose eq172867 eq9
    | exact resolve eq9 eq172867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208805 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq175816 X0
       have i₂ := eq172269 X0
       grind)
    | exact superpose eq172269 eq175816
    | exact resolve eq175816 eq172269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175816
  have eq505111 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq170866 X0 X1
       have i₂ := eq171761 X1
       grind)
    | exact superpose eq171761 eq170866
    | (have j0 := eq170866 X0 X1
       grind)
    | exact resolve eq170866 eq171761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170866 eq171761
  have eq505112 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq505111 X0 X1
       have i₂ := eq173805 X0
       grind)
    | exact superpose eq173805 eq505111
    | (have j0 := eq505111 X0 X1
       grind)
    | exact resolve eq505111 eq173805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173805 eq505111
  have eq505367 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X1))
       have i₂ := eq505112 X0 X1
       grind)
    | exact superpose eq505112 eq10
    | (have j1 := eq505112 X0 X1
       grind)
    | exact resolve eq10 eq505112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505112
  have eq507249 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (M.op (τ X1) X0) ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (τ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq505367 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq505367
    | (have j0 := eq505367 X1 (σ X0)
       grind)
    | exact resolve eq505367 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505367
  have eq508105 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (τ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq507249 X0 X1
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq507249
    | (have j0 := eq507249 X0 X1
       grind)
    | exact resolve eq507249 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq507249
  have eq508466 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (σ (M.op X0 X0)) = X1 ∨ (τ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq508105 X0 X1
       have i₂ := eq172867 X0
       grind)
    | exact superpose eq172867 eq508105
    | (have j0 := eq508105 X0 X1
       grind)
    | exact resolve eq508105 eq172867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508105
  have eq512356 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq508466 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq508466
    | (have j0 := eq508466 X1 (σ X0)
       grind)
    | exact resolve eq508466 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508466
  have eq513283 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq512356 X0 X1
       have i₂ := eq173818 X0
       grind)
    | exact superpose eq173818 eq512356
    | (have j0 := eq512356 X0 X1
       grind)
    | exact resolve eq512356 eq173818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173818 eq512356
  have eq515484 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq107
       have i₂ := eq513283 x y
       grind)
    | exact superpose eq513283 eq107
    | (have j1 := eq513283 x y
       grind)
    | exact resolve eq107 eq513283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq513283
  have eq515487 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq515484
  have eq515559 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq515487
       have i₂ := eq172867 y
       grind)
    | exact superpose eq172867 eq515487
    | exact resolve eq515487 eq172867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515487
  have eq515560 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq515559
  have eq516376 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq515560
       have i₂ := eq172867 x
       grind)
    | exact superpose eq172867 eq515560
    | exact resolve eq515560 eq172867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172867 eq515560
  have eq517934 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq172269 x
       have i₂ := eq516376
       grind)
    | exact superpose eq516376 eq172269
    | exact resolve eq172269 eq516376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516376
  have eq518037 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq517934
       have r₂ := eq16
       grind)
    | exact resolve eq517934 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517934
  have eq519116 : (M.op y y) = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq518037
       grind)
    | exact superpose eq518037 eq10
    | exact resolve eq10 eq518037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518037
  have eq520009 : x = (M.op y y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq519116
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq519116
    | exact resolve eq519116 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519116
  have eq520745 : (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq208805 y
       have i₂ := eq520009
       grind)
    | exact superpose eq520009 eq208805
    | exact resolve eq208805 eq520009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208805
  have eq520801 : (M.op x y) = (M.op y x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9 y y
       have i₂ := eq520009
       grind)
    | exact superpose eq520009 eq9
    | exact resolve eq9 eq520009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520009
  have eq529045 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq520745
       grind)
    | exact superpose eq520745 eq16
    | exact resolve eq16 eq520745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520745
  have eq529166 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq529045
       have i₂ := eq520801
       grind)
    | exact superpose eq520801 eq529045
    | exact resolve eq529045 eq520801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520801 eq529045
  have eq529170 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq529166
  have eq529171 : (σ y) = (σ (M.op x x)) := by grind
  clear eq529170
  have eq529229 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq529171
       grind)
    | exact superpose eq529171 eq10
    | exact resolve eq10 eq529171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529171
  have eq530123 : y = (M.op x x) := by
    first
    | (have i₁ := eq529229
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq529229
    | exact resolve eq529229 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529229
  have eq530850 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq172269 x
       have i₂ := eq530123
       grind)
    | exact superpose eq530123 eq172269
    | exact resolve eq172269 eq530123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172269 eq530123
  have eq530946 : False := by grind
  exact eq530946

/-- `Equation4511`: `x ◇ (y ◇ z) = (x ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_y_pyx_x_pyx_Equation4511 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4511 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4511.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X1) X1) := by
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
  have eq42 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq35 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq35
    | exact resolve eq35 eq15
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : (σ (k x (k x x))) = (k (σ x) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq35 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq35
    | exact resolve eq35 eq43
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
  have eq50 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X0 (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 (M.op X1 X2)) X1 X2
       have i₂ := eq14 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op X0 X1) X1) (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 X2) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X1) = (M.op (M.op X0 X1) (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X1) X1 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 X1 X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op (M.op X0 X1) X0) X0) ∨ (k (M.op X0 X1) X2) = (M.op X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 X1) X2
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X0 X1) X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq76 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq88 : ∀ X0 : G, (σ (k X0 (k y y))) = (k (σ X0) (k (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq10
    | exact resolve eq10 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq96 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq96 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq96
    | (have j0 := eq96 (σ X0) (σ X1)
       grind)
    | exact resolve eq96 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq96 y x
       grind)
    | exact superpose eq96 eq74
    | (have j1 := eq96 y x
       grind)
    | exact resolve eq74 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq111 : (k (σ y) (σ (M.op x y))) = (σ (M.op (M.op x y) y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq96 y sF0
       grind)
    | exact superpose eq96 eq76
    | (have j1 := eq96 y (M.op x y)
       grind)
    | exact resolve eq76 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq107
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107
    | exact resolve eq107 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq121
    | exact resolve eq121 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq123 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
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
  have eq131 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq211 : ∀ X0 X1 : G, (M.op x (M.op (M.op y X0) X1)) = (M.op (M.op (M.op x y) y) (M.op y X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x (M.op y X0) X1
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op (σ y) X0) X1)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq123 eq16
    | exact resolve eq16 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq408 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq56
    | (have j0 := eq56 X0 x X1 y
       grind)
    | exact resolve eq56 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq56
    | (have j0 := eq56 X0 (σ x) X1 (σ y)
       grind)
    | exact resolve eq56 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq408 X0 (M.op y x)
       have i₂ := eq54 x
       grind)
    | exact superpose eq54 eq408
    | exact resolve eq408 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459 : ∀ X0 : G, (M.op (M.op X0 x) x) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq408 X0 x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq408
    | (have j1 := eq14 X0 x y
       grind)
    | exact resolve eq408 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq55 eq410
    | exact resolve eq410 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq485 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq410 X0 x
       have i₂ := eq14 X0 sF2 x
       grind)
    | exact superpose eq14 eq410
    | (have j1 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq410 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op X0 (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq50 X1 X2 X0
       have i₂ := eq56 X0 (M.op X1 X2) X2 X3
       grind)
    | (have i₁ := eq50 X1 X2 X0
       have i₂ := eq56 X0 (M.op X1 X2) X3 X2
       grind)
    | exact superpose eq56 eq50
    | exact resolve eq50 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq452 X0
       have i₂ := eq56 X0 sF0 y x
       grind)
    | (have i₁ := eq452 X0
       have i₂ := eq56 X0 sF0 x y
       grind)
    | exact superpose eq56 eq452
    | exact resolve eq452 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq624 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq477 X0
       have i₂ := eq56 X0 sF4 sF3 x
       grind)
    | (have i₁ := eq477 X0
       have i₂ := eq56 X0 sF4 x sF3
       grind)
    | exact superpose eq56 eq477
    | exact resolve eq477 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X1) = (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 (M.op X1 X2) X3 X2
       have i₂ := eq50 X1 X2 (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq50 eq53
    | exact resolve eq53 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq826 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq583 X0 x
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq583
    | exact resolve eq583 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq881 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X0 X1 X2 X2
       have i₂ := eq50 X1 X2 X0
       grind)
    | exact superpose eq50 eq51
    | exact resolve eq51 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1047 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq624 X0 x
       have i₂ := eq14 X0 sF4 x
       grind)
    | exact superpose eq14 eq624
    | exact resolve eq624 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq1115 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (M.op X0 X1) X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X1 X2 X2
       have i₂ := eq50 X1 X2 X0
       grind)
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1119 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X1 X2)) = (M.op (M.op (M.op X0 X1) X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X1 X2 x
       have i₂ := eq14 X0 (M.op X1 X2) x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1357 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq100 X0 X0
       grind)
    | exact superpose eq100 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq100 X0 X0
       grind)
    | (have r₁ := eq13 (σ X1) X1
       have r₂ := eq100 X1 X1
       grind)
    | exact resolve eq13 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1371 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq100 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq1373 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1357 X0 X1
       have j1 := eq13 (σ X0) X1
       grind)
    | (have r₁ := eq1357 X0 X1
       have r₂ := eq13 (σ X0) X1
       grind)
    | exact resolve eq1357 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357
  have eq1682 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) ≠ (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) ∨ (M.op X0 (M.op (M.op x y) (M.op x y))) = (k (M.op (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq826 eq67
    | (have j0 := eq67 (M.op x y) (M.op x y) X0
       grind)
    | exact resolve eq67 eq826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1685 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 (M.op (M.op X0 X0) X1)) (M.op X0 X0)) ∨ (k (M.op (M.op X0 X0) X0) X2) = (M.op X2 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 (M.op X0 X0) X0 X2
       have i₂ := eq52 X0 X0 X0 X1
       grind)
    | exact superpose eq52 eq67
    | (have j0 := eq67 (M.op X0 X0) X0 X2
       grind)
    | exact resolve eq67 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1734 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (k (M.op (M.op X0 X0) X0) X2) ∨ (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 (M.op (M.op X0 X0) X1)) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1685 X0 X1 X2
       have i₂ := eq50 X0 X0 X2
       grind)
    | exact superpose eq50 eq1685
    | (have j0 := eq1685 X0 X1 X2
       grind)
    | exact resolve eq1685 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1685
  have eq1737 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (M.op x y))) = (k (M.op (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | (have j0 := eq1682 X0
       grind)
    | (have r₁ := eq1682 X0
       have r₂ := eq826 (M.op x y)
       grind)
    | exact resolve eq1682 eq826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826 eq1682
  have eq1757 : ∀ X0 : G, (M.op X0 (M.op x y)) = (k (M.op (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq583 eq1737
    | exact resolve eq1737 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583 eq1737
  have eq1770 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq122 eq96
    | (have j0 := eq96 (σ y) (σ x)
       grind)
    | exact resolve eq96 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq1771 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq1770
    | exact resolve eq1770 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1770
  have eq1774 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq1771
       have r₂ := eq27
       grind)
    | exact resolve eq1771 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1771
  have eq1832 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1774 eq485
    | exact resolve eq485 eq1774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1841 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq1774 eq56
    | exact resolve eq56 eq1774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1969 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ x) (σ x))) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1832 eq1841
    | exact resolve eq1841 eq1832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1841
  have eq2039 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ x) (σ x))) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq1969 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1969
  have eq2042 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq410 eq2039
    | exact resolve eq2039 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2039
  have eq2078 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2042 eq1832
    | exact resolve eq1832 eq2042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1832 eq2042
  have eq2084 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq2078
  have eq2107 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2084 eq1774
    | exact resolve eq1774 eq2084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084
  have eq2125 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq2107
  have eq2149 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2125 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq2125
       grind)
    | exact resolve eq13 eq2125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2161 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq2149 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2149
  have eq2227 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2161 eq49
    | exact resolve eq49 eq2161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq2228 : (k x y) = (τ (M.op (σ y) (σ x))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2161 eq61
    | exact resolve eq61 eq2161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq2161
  have eq2317 : (τ (σ x)) = (k x x) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2125 eq2227
    | exact resolve eq2227 eq2125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2125 eq2227
  have eq2330 : (τ (σ x)) = (k x x) ∨ x = (M.op y x) := by grind
  clear eq2317
  have eq2332 : x = (k x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28 eq2330
    | exact resolve eq2330 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2330
  have eq2552 : (τ (σ x)) = (k x y) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1774 eq2228
    | exact resolve eq2228 eq1774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774 eq2228
  have eq2565 : (τ (σ x)) = (k x y) ∨ x = (M.op y x) := by grind
  clear eq2552
  have eq2569 : x = (k x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28 eq2565
    | exact resolve eq2565 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2565
  have eq6288 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq211 X0 x
       have i₂ := eq542 x y X0 x
       grind)
    | exact superpose eq542 eq211
    | exact resolve eq211 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq6289 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq6288 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6288
    | (have j0 := eq6288 X0
       grind)
    | exact resolve eq6288 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6288
  have eq6360 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq6289 x
       have i₂ := eq53 sF0 y x x
       grind)
    | exact superpose eq53 eq6289
    | exact resolve eq6289 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6289
  have eq6483 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq217 x x
       have i₂ := eq542 sF2 sF3 x x
       grind)
    | exact superpose eq542 eq217
    | exact resolve eq217 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq542
  have eq6484 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq6483
    | (have j0 := eq6483 X0
       grind)
    | exact resolve eq6483 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6483
  have eq6577 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq6484 x
       have i₂ := eq53 sF4 sF3 x x
       grind)
    | exact superpose eq53 eq6484
    | exact resolve eq6484 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6484
  have eq10503 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq881 X0 X1 x
       have i₂ := eq53 X0 X1 x X2
       grind)
    | exact superpose eq53 eq881
    | exact resolve eq881 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10565 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op (M.op X0 X0) X0) ∨ (k (M.op X0 (M.op X0 X1)) X2) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X0 (M.op X0 X1) X2
       have i₂ := eq881 X0 X0 X1
       grind)
    | exact superpose eq881 eq67
    | (have j0 := eq67 X0 (M.op X0 X1) X2
       grind)
    | exact resolve eq67 eq881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq10671 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X0 X1)) X2) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq10565 X0 X1 X2
       grind)
    | (have r₁ := eq10565 X1 X2 X2
       have r₂ := eq14 X1 X1 X2
       grind)
    | exact resolve eq10565 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10565
  have eq10772 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (k (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10671 X0 X1 X2
       have i₂ := eq14 X2 X0 (M.op X0 X1)
       grind)
    | exact superpose eq14 eq10671
    | exact resolve eq10671 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10671
  have eq13311 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k (σ (τ X0)) X1) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1373 (τ X0) X1
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq1373
    | (have j0 := eq1373 (τ X0) X1
       grind)
    | exact resolve eq1373 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq13324 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k (σ (τ X0)) X1) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13311 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq13311
    | (have j0 := eq13311 X0 X1
       grind)
    | exact resolve eq13311 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13311
  have eq13343 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13324 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq13324
    | (have j0 := eq13324 X0 X1
       grind)
    | exact resolve eq13324 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13324
  have eq46098 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 (M.op X1 X2)) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1119 X0 X1 X2
       have i₂ := eq1115 X0 X1 X2
       grind)
    | exact superpose eq1115 eq1119
    | exact resolve eq1119 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119
  have eq66933 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq742 X0 X1 X2 X3
       have i₂ := eq881 X0 X1 X2
       grind)
    | exact superpose eq881 eq742
    | exact resolve eq742 eq881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq881
  have eq295578 : ∀ X0 X2 : G, (M.op (M.op X2 X0) X0) = (k (M.op (M.op X0 X0) X0) X2) := by
    intro X0 X2
    first
    | (have j0 := eq1734 X0 x X2
       grind)
    | (have r₁ := eq1734 X2 x X2
       have r₂ := eq66933 X2 X2 X2 x
       grind)
    | exact resolve eq1734 eq66933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734 eq66933
  have eq472366 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op X0 x) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq13343 x X0
       have i₂ := eq2332
       grind)
    | exact superpose eq2332 eq13343
    | (have j0 := eq13343 x X0
       grind)
    | (have r₁ := eq13343 x x
       have r₂ := eq2332
       grind)
    | exact resolve eq13343 eq2332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2332 eq13343
  have eq472386 : ∀ X0 : G, (k x X0) = (M.op X0 x) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq472366 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472366
  have eq472524 : x = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2569
       have i₂ := eq472386 y
       grind)
    | exact superpose eq472386 eq2569
    | exact resolve eq2569 eq472386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2569 eq472386
  have eq472554 : x = (M.op y x) := by grind
  clear eq472524
  have eq472610 : (M.op (M.op x y) y) = (M.op x x) := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq472554
       grind)
    | exact superpose eq472554 eq54
    | exact resolve eq54 eq472554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472613 : (M.op (M.op x y) y) = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq6360 x
       have i₂ := eq472554
       grind)
    | exact superpose eq472554 eq6360
    | exact resolve eq6360 eq472554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6360
  have eq472619 : (M.op x x) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq459 y
       have i₂ := eq472554
       grind)
    | exact superpose eq472554 eq459
    | exact resolve eq459 eq472554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472628 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 y x X1
       have i₂ := eq472554
       grind)
    | exact superpose eq472554 eq56
    | exact resolve eq56 eq472554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476423 : (M.op x x) = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq472610 eq472613
    | exact resolve eq472613 eq472610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472613
  have eq476796 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x x)) := by
    intro X0
    first
    | exact superpose eq472619 eq472628
    | exact resolve eq472628 eq472619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477277 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X1)) y) = (M.op (M.op X0 y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 y X1 x
       have i₂ := eq472628 (M.op X0 y) x
       grind)
    | exact superpose eq472628 eq53
    | exact resolve eq53 eq472628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq477856 : ∀ X0 : G, (M.op (M.op X0 x) y) = (M.op (M.op X0 y) x) := by
    intro X0
    first
    | (have i₁ := eq477277 X0 x
       have i₂ := eq472628 X0 x
       grind)
    | exact superpose eq472628 eq477277
    | exact resolve eq477277 eq472628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477277
  have eq478111 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq476796 X0
       have i₂ := eq408 X0 x
       grind)
    | exact superpose eq408 eq476796
    | exact resolve eq476796 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408 eq476796
  have eq479477 : (M.op x x) = (M.op y x) := by
    first
    | exact superpose eq478111 eq472619
    | exact resolve eq472619 eq478111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472619
  have eq479487 : ∀ X0 : G, (M.op X0 (M.op x y)) = (k (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | exact superpose eq478111 eq1757
    | exact resolve eq1757 eq478111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1757
  have eq479516 : ∀ X0 : G, (M.op X0 x) = (k (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | exact superpose eq478111 eq479487
    | exact resolve eq479487 eq478111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479487
  have eq479517 : x = (M.op x x) := by
    first
    | (have i₁ := eq479477
       have i₂ := eq472554
       grind)
    | exact superpose eq472554 eq479477
    | exact resolve eq479477 eq472554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479477
  have eq480867 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq479517
       grind)
    | exact superpose eq479517 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq479517
       grind)
    | exact resolve eq13 eq479517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq481071 : ∀ X0 : G, (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq480867 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480867
  have eq483152 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1373 x X0
       have i₂ := eq481071 x
       grind)
    | exact superpose eq481071 eq1373
    | (have j0 := eq1373 x X0
       grind)
    | exact resolve eq1373 eq481071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq483153 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1371 x
       have i₂ := eq481071 x
       grind)
    | exact superpose eq481071 eq1371
    | (have j0 := eq1371 x
       grind)
    | exact resolve eq1371 eq481071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq483171 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op (τ X0) x)) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq481071 (τ X0)
       grind)
    | exact superpose eq481071 eq42
    | exact resolve eq42 eq481071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq483190 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq481071 x
       grind)
    | exact superpose eq481071 eq43
    | exact resolve eq43 eq481071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq483208 : (k (σ x) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq481071 y
       grind)
    | exact superpose eq481071 eq44
    | exact resolve eq44 eq481071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq483228 : (k (σ x) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq481071 sF0
       grind)
    | exact superpose eq481071 eq45
    | exact resolve eq45 eq481071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq483253 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq483208
       have i₂ := eq472554
       grind)
    | exact superpose eq472554 eq483208
    | exact resolve eq483208 eq472554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483208
  have eq483260 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq483190
       have i₂ := eq479517
       grind)
    | exact superpose eq479517 eq483190
    | exact resolve eq483190 eq479517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483190
  have eq483282 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq483153
       have i₂ := eq479517
       grind)
    | exact superpose eq479517 eq483153
    | exact resolve eq483153 eq479517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483153
  have eq483283 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq483282
  have eq483284 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq483152 X0
       have i₂ := eq479517
       grind)
    | exact superpose eq479517 eq483152
    | (have j0 := eq483152 X0
       grind)
    | exact resolve eq483152 eq479517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483152
  have eq483285 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq483284 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483284
  have eq483293 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq483253
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq483253
    | exact resolve eq483253 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483253
  have eq483300 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq483260
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq483260
    | exact resolve eq483260 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483260
  have eq483311 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq483283
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq483283
    | exact resolve eq483283 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483283
  have eq483312 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq483285 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq483285
    | (have j0 := eq483285 X0
       grind)
    | exact resolve eq483285 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483285
  have eq483967 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq483311 eq410
    | exact resolve eq410 eq483311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq484796 : (σ (k (k x (k x x)) (k y y))) = (k (k (σ x) (k (σ x) (σ x))) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq88 (k x (k x x))
       have i₂ := eq46
       grind)
    | exact superpose eq46 eq88
    | exact resolve eq88 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq88
  have eq484971 : (k (k (σ x) (σ x)) (k (σ y) (σ y))) = (σ (k (k x (k x x)) (k y y))) := by
    first
    | exact superpose eq483300 eq484796
    | exact resolve eq484796 eq483300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484796
  have eq485069 : (k (k (σ x) (σ x)) (k (σ y) (σ y))) = (σ (k (M.op (k x x) x) (k y y))) := by
    first
    | (have i₁ := eq484971
       have i₂ := eq481071 (k x x)
       grind)
    | exact superpose eq481071 eq484971
    | exact resolve eq484971 eq481071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484971
  have eq485119 : (k (k (σ x) (σ x)) (k (σ y) (σ y))) = (σ (k (M.op (M.op x x) x) (k y y))) := by
    first
    | (have i₁ := eq485069
       have i₂ := eq481071 x
       grind)
    | exact superpose eq481071 eq485069
    | exact resolve eq485069 eq481071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481071 eq485069
  have eq485137 : (k (k (σ x) (σ x)) (k (σ y) (σ y))) = (σ (M.op (M.op (k y y) x) x)) := by
    first
    | (have i₁ := eq485119
       have i₂ := eq295578 x (k y y)
       grind)
    | exact superpose eq295578 eq485119
    | exact resolve eq485119 eq295578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295578 eq485119
  have eq485147 : (σ (M.op (k y y) (M.op x y))) = (k (k (σ x) (σ x)) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq485137
       have i₂ := eq459 (k y y)
       grind)
    | exact superpose eq459 eq485137
    | exact resolve eq485137 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459 eq485137
  have eq485153 : (k (σ x) (k (σ y) (σ y))) = (σ (M.op (k y y) (M.op x y))) := by
    first
    | exact superpose eq483300 eq485147
    | exact resolve eq485147 eq483300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483300 eq485147
  have eq485159 : (k (σ x) (k (σ y) (σ y))) = (σ (M.op (k y y) x)) := by
    first
    | exact superpose eq478111 eq485153
    | exact resolve eq485153 eq478111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485153
  have eq487446 : (k (σ y) (σ (M.op x y))) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq472610 eq111
    | exact resolve eq111 eq472610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq487447 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq487446
       have i₂ := eq479517
       grind)
    | exact superpose eq479517 eq487446
    | exact resolve eq487446 eq479517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487446
  have eq487448 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq487447
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq487447
    | exact resolve eq487447 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487447
  have eq487449 : (M.op x y) = (M.op y x) ∨ (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq478111 eq487448
    | exact resolve eq487448 eq478111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478111 eq487448
  have eq487450 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq487449
       have i₂ := eq472554
       grind)
    | exact superpose eq472554 eq487449
    | exact resolve eq487449 eq472554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487449
  have eq487524 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq483293 eq483312
    | exact resolve eq483312 eq483293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483293
  have eq487781 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq487524 eq55
    | exact resolve eq55 eq487524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq488164 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq483311 eq487781
    | exact resolve eq487781 eq483311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483311 eq487781
  have eq489142 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq488164 eq1115
    | exact resolve eq1115 eq488164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq489351 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq489142
    | (have j0 := eq489142 X0
       grind)
    | exact resolve eq489142 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489142
  have eq495472 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq487524 eq489351
    | exact resolve eq489351 eq487524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487524
  have eq497485 : (σ (M.op (M.op x y) x)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq483312 eq483228
    | exact resolve eq483228 eq483312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483228
  have eq498256 : x = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq476423
       have i₂ := eq479517
       grind)
    | exact superpose eq479517 eq476423
    | exact resolve eq476423 eq479517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476423
  have eq498405 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq498256 eq1115
    | exact resolve eq1115 eq498256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115 eq498256
  have eq498622 : (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq498405 x
       have i₂ := eq472628 (M.op x y) x
       grind)
    | exact superpose eq472628 eq498405
    | exact resolve eq498405 eq472628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498405
  have eq498867 : (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq498622
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq498622
    | exact resolve eq498622 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498622
  have eq499906 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq498867 eq497485
    | exact resolve eq497485 eq498867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq500248 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq499906
    | exact resolve eq499906 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499906
  have eq513134 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ y) X1))) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X1))) = (k (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X1)) (M.op (M.op (σ x) (σ y)) (σ y))) X0) := by
    intro X0 X1
    first
    | exact superpose eq6577 eq10772
    | exact resolve eq10772 eq6577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6577
  have eq513599 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ y) X1))) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X1))) = (k (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X1)) (M.op (σ x) (σ y))) X0) := by
    intro X0 X1
    first
    | exact superpose eq477 eq513134
    | exact resolve eq513134 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477 eq513134
  have eq513946 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ y) X1))) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X1))) = (k (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X1)) (σ x)) X0) := by
    intro X0 X1
    first
    | exact superpose eq483967 eq513599
    | exact resolve eq513599 eq483967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513599
  have eq514138 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) = (k (M.op (M.op (σ x) (σ y)) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq489351 eq513946
    | exact resolve eq513946 eq489351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489351 eq513946
  have eq514228 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq495472 eq514138
    | exact resolve eq514138 eq495472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514138
  have eq514256 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq1047 eq514228
    | exact resolve eq514228 eq1047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047 eq514228
  have eq514270 : ∀ X0 : G, (M.op X0 (σ x)) = (k (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq483967 eq514256
    | exact resolve eq514256 eq483967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514256
  have eq514288 : ∀ X0 : G, (σ (M.op (σ x) (σ y))) ≠ (σ (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (k (σ (M.op (σ x) (σ y))) X0) = (M.op X0 (σ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq514270 eq1373
    | (have j0 := eq1373 (M.op (σ x) (σ y)) X0
       grind)
    | exact resolve eq1373 eq514270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq514318 : ∀ X0 : G, (σ (M.op (σ x) (σ y))) ≠ (σ (M.op (σ x) (σ y))) ∨ (k (σ (M.op (σ x) (σ y))) X0) = (M.op X0 (σ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq495472 eq514288
    | (have j0 := eq514288 X0
       grind)
    | exact resolve eq514288 eq495472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514288
  have eq514319 : ∀ X0 : G, (k (σ (M.op (σ x) (σ y))) X0) = (M.op X0 (σ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have j0 := eq514318 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514318
  have eq514764 : (M.op (σ y) (σ (M.op (σ x) (σ y)))) = (σ (k (M.op (σ x) (σ y)) y)) := by
    first
    | exact superpose eq514319 eq40
    | exact resolve eq40 eq514319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514319
  have eq514765 : (σ (M.op y (σ x))) = (M.op (σ y) (σ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq514270 eq514764
    | exact resolve eq514764 eq514270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514270 eq514764
  have eq517823 : ∀ X0 : G, (k (M.op x y) X0) = (M.op X0 x) := by
    intro X0
    first
    | exact superpose eq498867 eq479516
    | exact resolve eq479516 eq498867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479516 eq498867
  have eq517827 : ∀ X0 : G, (M.op (τ X0) x) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq281 eq517823
    | exact resolve eq517823 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq517849 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op (M.op x y) x)) ∨ (k (σ (M.op x y)) X0) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq517823 eq1373
    | (have j0 := eq1373 (M.op x y) X0
       grind)
    | exact resolve eq1373 eq517823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq517850 : (σ (M.op x y)) ≠ (σ (M.op (M.op x y) x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq517823 eq1371
    | (have j0 := eq1371 (M.op x y)
       grind)
    | exact resolve eq1371 eq517823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371
  have eq517903 : (σ (M.op y x)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq517823 eq131
    | exact resolve eq131 eq517823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq517919 : (σ (M.op (M.op x y) x)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq517823 eq132
    | exact resolve eq132 eq517823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq517823
  have eq517941 : (M.op (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq497485 eq517919
    | exact resolve eq517919 eq497485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517919
  have eq517950 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq517903
       have i₂ := eq472554
       grind)
    | exact superpose eq472554 eq517903
    | exact resolve eq517903 eq472554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517903
  have eq517984 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq497485 eq517850
    | exact resolve eq517850 eq497485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517850
  have eq517985 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ x)) ∨ (k (σ (M.op x y)) X0) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq497485 eq517849
    | (have j0 := eq517849 X0
       grind)
    | exact resolve eq517849 eq497485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497485 eq517849
  have eq517996 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq500248 eq517941
    | exact resolve eq517941 eq500248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517941
  have eq518005 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq517950
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq517950
    | exact resolve eq517950 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517950
  have eq518029 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq500248 eq517984
    | (have r₁ := eq517984
       have r₂ := eq500248
       grind)
    | exact resolve eq517984 eq500248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517984
  have eq518030 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ (M.op x y)) X0) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq500248 eq517985
    | (have j0 := eq517985 X0
       grind)
    | (have r₁ := eq517985 X0
       have r₂ := eq500248
       grind)
    | exact resolve eq517985 eq500248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517985
  have eq518057 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq518029
       have r₂ := eq20
       grind)
    | exact resolve eq518029 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518029
  have eq518058 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq518030 X0
       grind)
    | (have r₁ := eq518030 X0
       have r₂ := eq20
       grind)
    | exact resolve eq518030 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518030
  have eq518075 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq518057
    | exact resolve eq518057 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518057
  have eq518076 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq518058
    | (have j0 := eq518058 X0
       grind)
    | exact resolve eq518058 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518058
  have eq518131 : ∀ X0 : G, (σ (σ (M.op x y))) ≠ (σ (σ (M.op x y))) ∨ (k (σ (σ (M.op x y))) X0) = (M.op X0 (σ (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq517996 eq1373
    | (have j0 := eq1373 (σ (M.op x y)) X0
       grind)
    | exact resolve eq1373 eq517996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1373 eq517996
  have eq518147 : ∀ X0 : G, (k (σ (σ (M.op x y))) X0) = (M.op X0 (σ (σ (M.op x y)))) := by
    intro X0
    first
    | (have j0 := eq518131 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518131
  have eq518464 : ∀ X0 : G, (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq518075 eq10772
    | exact resolve eq10772 eq518075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10772
  have eq518556 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq518075 eq518464
    | exact resolve eq518464 eq518075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518075 eq518464
  have eq518739 : (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq518005 eq518076
    | exact resolve eq518076 eq518005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518005
  have eq519712 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq518739 eq56
    | exact resolve eq56 eq518739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq519846 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = (M.op (M.op X0 (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq518739 eq46098
    | exact resolve eq46098 eq518739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46098
  have eq519966 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq485 eq519846
    | exact resolve eq519846 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485 eq519846
  have eq520118 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op X0 (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq483967 eq519966
    | exact resolve eq519966 eq483967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483967 eq519966
  have eq525571 : ∀ X0 : G, (M.op (τ X0) x) = (τ (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq518076 eq517827
    | exact resolve eq517827 eq518076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517827
  have eq526749 : ∀ X0 : G, (k (σ x) X0) = (σ (τ (M.op X0 (σ (M.op x y))))) := by
    intro X0
    first
    | (have i₁ := eq483171 X0
       have i₂ := eq525571 X0
       grind)
    | exact superpose eq525571 eq483171
    | exact resolve eq483171 eq525571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483171 eq525571
  have eq526750 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq526749 X0
       have i₂ := eq15 (M.op X0 sF1)
       grind)
    | exact superpose eq15 eq526749
    | exact resolve eq526749 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526749
  have eq526751 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq483312 eq526750
    | exact resolve eq526750 eq483312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526750
  have eq526839 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq495472 eq526751
    | exact resolve eq526751 eq495472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495472
  have eq535152 : (σ (k (σ (M.op x y)) y)) = (M.op (σ y) (σ (σ (M.op x y)))) := by
    first
    | exact superpose eq518147 eq40
    | exact resolve eq40 eq518147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq518147
  have eq535153 : (M.op (σ y) (σ (σ (M.op x y)))) = (σ (M.op y (σ (M.op x y)))) := by
    first
    | exact superpose eq518076 eq535152
    | exact resolve eq535152 eq518076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535152
  have eq536919 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq518076 eq518556
    | exact resolve eq518556 eq518076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518076 eq518556
  have eq539798 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op X0 (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq526751 eq519712
    | exact resolve eq519712 eq526751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519712
  have eq539801 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq526751 eq520118
    | exact resolve eq520118 eq526751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520118
  have eq542079 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (σ (M.op y (σ (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq535153 eq539798
    | exact resolve eq539798 eq535153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535153
  have eq645367 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (M.op (M.op X0 (σ y)) (σ (M.op y (σ x)))) (σ y)) := by
    intro X0
    first
    | exact superpose eq514765 eq10503
    | exact resolve eq10503 eq514765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10503 eq514765
  have eq646810 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (M.op (M.op X0 (σ y)) (σ (M.op y (σ (M.op x y))))) (σ y)) := by
    intro X0
    first
    | exact superpose eq526751 eq645367
    | exact resolve eq645367 eq526751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645367
  have eq648043 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (M.op (M.op X0 (σ y)) (σ (M.op x y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq542079 eq646810
    | exact resolve eq646810 eq542079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542079 eq646810
  have eq648757 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op (M.op (M.op X0 (σ y)) (σ (M.op x y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq539801 eq648043
    | exact resolve eq648043 eq539801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539801 eq648043
  have eq663753 : ∀ X0 X1 : G, (M.op (M.op X0 (σ (M.op x y))) (σ y)) = (M.op (M.op (M.op X0 (σ y)) (σ (M.op x y))) (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq648757 eq14
    | exact resolve eq14 eq648757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648757
  have eq664130 : ∀ X0 : G, (M.op (M.op X0 (σ (M.op x y))) (σ y)) = (M.op (M.op (M.op X0 (σ y)) (σ (M.op x y))) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq539798 eq663753
    | exact resolve eq663753 eq539798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663753
  have eq664374 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ (M.op x y))) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq536919 eq664130
    | exact resolve eq664130 eq536919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536919 eq664130
  have eq731975 : (M.op (k (σ y) (σ y)) (σ x)) = (σ (M.op (k y y) x)) := by
    first
    | exact superpose eq483312 eq485159
    | exact resolve eq485159 eq483312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485159
  have eq731976 : (M.op (k (σ y) (σ y)) (σ (M.op x y))) = (σ (M.op (k y y) x)) := by
    first
    | exact superpose eq526751 eq731975
    | exact resolve eq731975 eq526751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526751 eq731975
  have eq739673 : (M.op (k (σ y) (σ y)) (σ (M.op x y))) = (σ (M.op (M.op y y) x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq731976
       have i₂ := eq96 y y
       grind)
    | exact superpose eq96 eq731976
    | (have j1 := eq96 y y
       grind)
    | exact resolve eq731976 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731976
  have eq739816 : (M.op (k (σ y) (σ y)) (σ (M.op x y))) = (σ (M.op (M.op y x) y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq739673
       have i₂ := eq477856 y
       grind)
    | exact superpose eq477856 eq739673
    | exact resolve eq739673 eq477856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477856 eq739673
  have eq739849 : (σ (M.op x y)) = (M.op (k (σ y) (σ y)) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq739816
       have i₂ := eq472554
       grind)
    | exact superpose eq472554 eq739816
    | exact resolve eq739816 eq472554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739816
  have eq739879 : (σ (M.op x y)) = (M.op (k (σ y) (σ y)) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq739849
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq739849
    | exact resolve eq739849 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739849
  have eq739903 : (σ (M.op x y)) = (M.op (k (σ y) (σ y)) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq739879
    | exact resolve eq739879 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739879
  have eq755332 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ y)) (σ (M.op x y))) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq739903
       have i₂ := eq96 sF3 sF3
       grind)
    | exact superpose eq96 eq739903
    | (have j1 := eq96 (M.op (σ y) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq739903 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq739903
  have eq755728 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ (M.op x y))) (σ y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq664374 eq755332
    | exact resolve eq755332 eq664374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664374 eq755332
  have eq755811 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq518739 eq755728
    | exact resolve eq755728 eq518739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755728
  have eq755849 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq755811
    | exact resolve eq755811 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755811
  have eq755872 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq755849
       have r₂ := eq27
       grind)
    | exact resolve eq755849 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755849
  have eq755904 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq755872 eq55
    | exact resolve eq55 eq755872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq755924 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq755872 eq14
    | exact resolve eq14 eq755872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq756270 : (M.op (σ y) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq539798 eq755924
    | exact resolve eq755924 eq539798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539798 eq755924
  have eq756285 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq488164 eq755904
    | exact resolve eq755904 eq488164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755904
  have eq756402 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq518739 eq756270
    | exact resolve eq756270 eq518739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518739 eq756270
  have eq756411 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq756285
    | exact resolve eq756285 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq756285
  have eq756667 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54 y
       have i₂ := eq756411
       grind)
    | exact superpose eq756411 eq54
    | exact resolve eq54 eq756411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq756685 : ∀ X0 : G, (M.op y y) = (M.op y (M.op y X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq756411
       grind)
    | exact superpose eq756411 eq14
    | exact resolve eq14 eq756411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757031 : (M.op y x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq756685 x
       have i₂ := eq472628 y x
       grind)
    | exact superpose eq472628 eq756685
    | exact resolve eq756685 eq472628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472628 eq756685
  have eq757044 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq472610 eq756667
    | exact resolve eq756667 eq472610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756667
  have eq757161 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq757031
       have i₂ := eq472554
       grind)
    | exact superpose eq472554 eq757031
    | exact resolve eq757031 eq472554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472554 eq757031
  have eq757169 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq757044
       have i₂ := eq479517
       grind)
    | exact superpose eq479517 eq757044
    | exact resolve eq757044 eq479517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757044
  have eq757276 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq757169
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq757169
    | exact resolve eq757169 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757169
  have eq757439 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq757276 eq27
    | exact resolve eq27 eq757276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757276
  have eq757727 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq756411
       have i₂ := eq757161
       grind)
    | exact superpose eq757161 eq756411
    | exact resolve eq756411 eq757161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756411 eq757161
  have eq757967 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq757727
  have eq758774 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq757967 eq27
    | exact resolve eq27 eq757967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757967
  have eq760643 : (σ x) = (σ y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq756402 eq755872
    | exact resolve eq755872 eq756402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755872 eq756402
  have eq760886 : y = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq760643
  have eq761853 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq54 y
       have i₂ := eq760886
       grind)
    | exact superpose eq760886 eq54
    | exact resolve eq54 eq760886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq760886
  have eq762230 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq472610 eq761853
    | exact resolve eq761853 eq472610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472610 eq761853
  have eq762355 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq762230
       have i₂ := eq479517
       grind)
    | exact superpose eq479517 eq762230
    | exact resolve eq762230 eq479517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479517 eq762230
  have eq762462 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq762355
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq762355
    | exact resolve eq762355 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq762355
  have eq762863 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq762462 eq487450
    | exact resolve eq487450 eq762462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487450 eq762462
  have eq762938 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq762863
  have eq762977 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq483312 eq762938
    | exact resolve eq762938 eq483312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483312 eq762938
  have eq763060 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq500248 eq762977
    | exact resolve eq762977 eq500248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500248 eq762977
  have eq763125 : x = (M.op x y) := by
    first
    | (have r₁ := eq763060
       have r₂ := eq757439
       grind)
    | exact resolve eq763060 eq757439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757439 eq763060
  have eq763205 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq763125 eq20
    | exact resolve eq20 eq763125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq763125
  have eq763598 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq763205
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq763205
    | exact resolve eq763205 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763205
  have eq764254 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq763598 eq758774
    | (have r₁ := eq758774
       have r₂ := eq763598
       grind)
    | exact resolve eq758774 eq763598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758774
  have eq764257 : x = y := by grind
  clear eq764254
  have eq764702 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq764257
       grind)
    | exact superpose eq764257 eq24
    | exact resolve eq24 eq764257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq764257
  have eq764993 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq764702
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq764702
    | exact resolve eq764702 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq764702
  have eq765075 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq763598 eq764993
    | exact resolve eq764993 eq763598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764993
  have eq765536 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq765075 eq488164
    | exact resolve eq488164 eq765075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488164 eq765075
  have eq765650 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq526839 eq765536
    | exact resolve eq765536 eq526839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526839 eq765536
  have eq765854 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq763598 eq765650
    | exact resolve eq765650 eq763598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763598 eq765650
  have eq766025 : False := by grind
  exact eq766025

/-- `Equation4608`: `(x ◇ x) ◇ y = (y ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_pxx_pxy_Equation4608 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4608 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4608.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
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
  have eq114 : (k y x) = (τ (k (σ y) (σ x))) := by
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
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
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
  have eq297 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq340 : ∀ X0 : G, (k (σ X0) (k (σ y) (σ y))) = (σ (k X0 (k y y))) := by
    intro X0
    first
    | exact superpose eq115 eq38
    | exact resolve eq38 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq381 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq297 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq297
    | exact resolve eq297 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq511 : ∀ X0 : G, (τ (k X0 (k (σ y) (σ y)))) = (k (τ X0) (k y y)) := by
    intro X0
    first
    | exact superpose eq115 eq381
    | exact resolve eq381 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq1107 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1109 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op (k X0 X0) X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1112 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
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
  have eq1113 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq1115 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1116 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1115 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115
  have eq1118 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op (k X0 X0) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1109 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109
  have eq1120 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1107 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq1121 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1120 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq1120 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq1120 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq1124 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1116 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1116
    | (have j0 := eq1116 (σ X0)
       grind)
    | exact resolve eq1116 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1126 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1121 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1121
    | (have j0 := eq1121 (σ X0) X1
       grind)
    | exact resolve eq1121 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1121
  have eq3328 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1112
       grind)
    | exact superpose eq1112 eq40
    | exact resolve eq40 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112
  have eq3329 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3328
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3328
    | exact resolve eq3328 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3328
  have eq3332 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq3329
    | exact resolve eq3329 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3329
  have eq14431 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3332 eq1113
    | exact resolve eq1113 eq3332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113 eq3332
  have eq14438 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq14431
       have r₂ := eq27
       grind)
    | exact resolve eq14431 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14431
  have eq14446 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq14438 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) x
       have r₂ := eq14438
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq14438
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq14438
       grind)
    | exact resolve eq13 eq14438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14450 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq14446 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14446
  have eq14475 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq14450 eq14438
    | exact resolve eq14438 eq14450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14438 eq14450
  have eq14476 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq14475
  have eq14504 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq14476 eq152
    | exact resolve eq152 eq14476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq14476
  have eq14511 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq31 eq14504
    | exact resolve eq14504 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq14504
  have eq14516 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq1116 (σ x)
       grind)
    | (have r₁ := eq14511
       have r₂ := eq1116 y
       grind)
    | exact resolve eq14511 eq1116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14511
  have eq14521 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq14516 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq14516
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq14516
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq14516
       grind)
    | exact resolve eq13 eq14516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14525 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq14521 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14521
  have eq14547 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq14525 eq14516
    | exact resolve eq14516 eq14525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14516 eq14525
  have eq14548 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq14547
  have eq14568 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq14548 eq141
    | exact resolve eq141 eq14548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq14548
  have eq14575 : x = (k x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq14568
    | exact resolve eq14568 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14568
  have eq14580 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq1116 y
       grind)
    | (have r₁ := eq14575
       have r₂ := eq1116 x
       grind)
    | exact resolve eq14575 eq1116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116 eq14575
  have eq14585 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq14580
       grind)
    | exact superpose eq14580 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq14580
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq14580
       grind)
    | exact resolve eq13 eq14580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14589 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq14585 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14585
  have eq14613 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq14589 x
       grind)
    | exact superpose eq14589 eq18
    | (have j1 := eq14589 x
       grind)
    | exact resolve eq18 eq14589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14614 : y = (k y y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14580
       have i₂ := eq14589 y
       grind)
    | exact superpose eq14589 eq14580
    | exact resolve eq14580 eq14589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14580 eq14589
  have eq14615 : y = (k y y) ∨ x = (M.op x x) := by grind
  clear eq14614
  have eq14635 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq14613
       grind)
    | exact superpose eq14613 eq39
    | exact resolve eq39 eq14613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14613
  have eq14636 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14635
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14635
    | exact resolve eq14635 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14635
  have eq14640 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq14636
    | exact resolve eq14636 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14636
  have eq14646 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1124 y
       have i₂ := eq14615
       grind)
    | exact superpose eq14615 eq1124
    | (have j0 := eq1124 y
       grind)
    | exact resolve eq1124 eq14615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14615
  have eq14651 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq14646
  have eq14652 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14651
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14651
    | exact resolve eq14651 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14651
  have eq14677 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq14652 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) x
       have r₂ := eq14652
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq14652
       grind)
    | exact resolve eq13 eq14652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14652
  have eq14681 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq14677 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14677
  have eq14723 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq14681 eq26
    | (have j1 := eq14681 (σ x)
       grind)
    | exact resolve eq26 eq14681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14681
  have eq14730 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq14640 eq14723
    | exact resolve eq14723 eq14640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14640 eq14723
  have eq14744 : x = (M.op x x) := by
    first
    | (have r₁ := eq14730
       have r₂ := eq27
       grind)
    | exact resolve eq14730 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14730
  have eq14749 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq14744
       grind)
    | exact superpose eq14744 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq14744
       grind)
    | exact resolve eq12 eq14744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14750 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq14744
       grind)
    | exact superpose eq14744 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq14744
       grind)
    | exact resolve eq13 eq14744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14754 : ∀ X0 : G, (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq14750 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14750
  have eq14755 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq14749 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14749
  have eq14775 : ∀ X0 : G, (M.op (M.op x x) X0) = (k x (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1118 X0 x
       have i₂ := eq14754 (k X0 X0)
       grind)
    | exact superpose eq14754 eq1118
    | (have j0 := eq1118 X0 x
       grind)
    | exact resolve eq1118 eq14754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14776 : x = (k x x) := by
    first
    | (have i₁ := eq14744
       have i₂ := eq14754 x
       grind)
    | exact superpose eq14754 eq14744
    | exact resolve eq14744 eq14754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14754
  have eq14777 : ∀ X0 : G, (M.op x X0) = (k x (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14775 X0
       have i₂ := eq14744
       grind)
    | exact superpose eq14744 eq14775
    | (have j0 := eq14775 X0
       grind)
    | exact resolve eq14775 eq14744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14744 eq14775
  have eq14796 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq14776
       grind)
    | exact superpose eq14776 eq39
    | exact resolve eq39 eq14776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14797 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1124 x
       have i₂ := eq14776
       grind)
    | exact superpose eq14776 eq1124
    | (have j0 := eq1124 x
       grind)
    | exact resolve eq1124 eq14776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14776
  have eq14802 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq14797
  have eq14803 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14802
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14802
    | exact resolve eq14802 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14802
  have eq14804 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq14796
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14796
    | exact resolve eq14796 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14796
  have eq14811 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq14803 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq14803
       grind)
    | exact resolve eq12 eq14803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14812 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq14803 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq14803
       grind)
    | exact resolve eq13 eq14803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14816 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq14812 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14812
  have eq14817 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq14811 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14811
  have eq14824 : (σ (σ x)) ≠ (σ (σ x)) ∨ (σ (σ x)) = (M.op (σ (σ x)) (σ (σ x))) := by
    first
    | exact superpose eq14804 eq1124
    | (have j0 := eq1124 (σ x)
       grind)
    | exact resolve eq1124 eq14804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124 eq14804
  have eq14829 : (σ (σ x)) = (M.op (σ (σ x)) (σ (σ x))) := by grind
  clear eq14824
  have eq15070 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = (k (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq14816 eq16
    | exact resolve eq16 eq14816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15071 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = (k (σ x) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq14816 eq1118
    | (have j0 := eq1118 X0 x
       grind)
    | exact resolve eq1118 eq14816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118 eq14816
  have eq15074 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq14803 eq15071
    | (have j0 := eq15071 X0
       grind)
    | exact resolve eq15071 eq14803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15071
  have eq15075 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq14803 eq15070
    | exact resolve eq15070 eq14803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14803 eq15070
  have eq15095 : ∀ X0 : G, (σ (σ x)) ≠ (σ (σ x)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 (σ (σ x))) := by
    intro X0
    first
    | exact superpose eq14829 eq12
    | (have j0 := eq12 X0 (σ (σ x))
       grind)
    | (have r₁ := eq12 X0 (σ (σ x))
       have r₂ := eq14829
       grind)
    | exact resolve eq12 eq14829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14829
  have eq15102 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 (σ (σ x))) := by
    intro X0
    first
    | (have j0 := eq15095 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15095
  have eq15107 : ∀ X0 : G, (k X0 x) = (k X0 (σ (σ x))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq14755 eq15102
    | (have j0 := eq15102 X0
       have j1 := eq14755 X0
       grind)
    | exact resolve eq15102 eq14755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15102
  have eq15901 : ∀ X0 : G, (k X0 x) = (k X0 X0) ∨ (k X0 x) = X0 ∨ (k X0 x) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq14755 X0
       grind)
    | exact superpose eq14755 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq14755 X0
       grind)
    | exact resolve eq11 eq14755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15921 : ∀ X0 : G, (k X0 x) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq14755 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15922 : ∀ X0 : G, (k X0 x) = (k X0 X0) ∨ (k X0 x) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq15901 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15901
  have eq15926 : ∀ X0 : G, (k X0 x) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq15922 X0
       have j1 := eq15921 X0
       grind)
    | (have r₁ := eq15922 X0
       have r₂ := eq15921 X0
       grind)
    | exact resolve eq15922 eq15921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15921 eq15922
  have eq15962 : (τ (k (σ y) (σ y))) = (k y (τ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq107 x
       have i₂ := eq15926 sF3
       grind)
    | (have i₁ := eq107 sF3
       have i₂ := eq15926 sF3
       grind)
    | exact superpose eq15926 eq107
    | (have j1 := eq15926 (σ y)
       grind)
    | exact resolve eq107 eq15926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16033 : (σ (k y x)) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq15926 y
       grind)
    | (have i₁ := eq36 x
       have i₂ := eq15926 y
       grind)
    | exact superpose eq15926 eq36
    | (have j1 := eq15926 y
       grind)
    | exact resolve eq36 eq15926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15926
  have eq16043 : (σ (k y x)) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16033
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16033
    | exact resolve eq16033 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16033
  have eq16108 : (k y y) = (k y (τ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq115 eq15962
    | exact resolve eq15962 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15962
  have eq16113 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16043
       have i₂ := eq39 y
       grind)
    | exact superpose eq39 eq16043
    | exact resolve eq16043 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16043
  have eq16173 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16113
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16113
    | exact resolve eq16113 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16113
  have eq16324 : ∀ X0 : G, (k X0 x) = (k X0 (σ x)) ∨ (k X0 (σ x)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14755 X0
       have i₂ := eq14817 X0
       grind)
    | exact superpose eq14817 eq14755
    | (have j0 := eq14755 X0
       have j1 := eq14817 X0
       grind)
    | exact resolve eq14755 eq14817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14755
  have eq16331 : ∀ X0 : G, (k X0 (σ x)) = (k X0 X0) ∨ (k X0 (σ x)) = X0 ∨ (k X0 (σ x)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq14817 X0
       grind)
    | exact superpose eq14817 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq14817 X0
       grind)
    | exact resolve eq11 eq14817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16350 : ∀ X0 : G, (k X0 (σ x)) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq14817 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14817
  have eq16351 : ∀ X0 : G, (k X0 (σ x)) = (k X0 X0) ∨ (k X0 (σ x)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq16331 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16331
  have eq16356 : ∀ X0 : G, (k X0 (σ x)) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq16351 X0
       have j1 := eq16350 X0
       grind)
    | (have r₁ := eq16351 X0
       have r₂ := eq16350 X0
       grind)
    | exact resolve eq16351 eq16350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16351
  have eq16359 : ∀ X0 : G, (k X0 x) = (k X0 (σ x)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq16324 X0
       have j1 := eq16350 X0
       grind)
    | (have r₁ := eq16324 X0
       have r₂ := eq16350 X0
       grind)
    | exact resolve eq16324 eq16350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16324 eq16350
  have eq16500 : (k y y) = (τ (k (σ y) (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq115
       have i₂ := eq16356 sF3
       grind)
    | exact superpose eq16356 eq115
    | (have j1 := eq16356 (σ y)
       grind)
    | exact resolve eq115 eq16356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq16509 : (k y x) = (k y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq114 eq16500
    | exact resolve eq16500 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16500
  have eq16784 : (τ (k (σ y) (σ x))) = (k y (τ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq107 x
       have i₂ := eq16359 sF3
       grind)
    | exact superpose eq16359 eq107
    | (have j1 := eq16359 (σ y)
       grind)
    | exact resolve eq107 eq16359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16359
  have eq16791 : (k y x) = (k y (τ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq114 eq16784
    | exact resolve eq16784 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq16784
  have eq17351 : (τ (k (σ y) x)) = (k y (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq15107 eq47
    | (have j1 := eq15107 (σ y)
       grind)
    | exact resolve eq47 eq15107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq15107
  have eq17377 : (k y (τ x)) = (k y (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq107 eq17351
    | exact resolve eq17351 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq17351
  have eq17635 : (k y x) = (k y (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16791
       have i₂ := eq17377
       grind)
    | exact superpose eq17377 eq16791
    | exact resolve eq16791 eq17377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16791
  have eq17636 : (k y y) = (k y (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16108
       have i₂ := eq17377
       grind)
    | exact superpose eq17377 eq16108
    | exact resolve eq16108 eq17377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16108 eq17377
  have eq17644 : (k y y) = (k y (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq17636
  have eq17645 : (k y x) = (k y (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq17635
  have eq17674 : (k (σ y) (σ y)) = (σ (k y (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq17644
       grind)
    | exact superpose eq17644 eq40
    | exact resolve eq40 eq17644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq17644
  have eq17689 : (k (σ y) (σ y)) = (k (σ y) (σ (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq17674
       have i₂ := eq36 sF2
       grind)
    | exact superpose eq36 eq17674
    | exact resolve eq17674 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17674
  have eq17696 : (k (σ y) (σ y)) = (k (σ y) (σ (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq17689
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17689
    | exact resolve eq17689 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17689
  have eq17703 : (k (σ y) (σ x)) = (k (σ y) (σ (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq16356 eq17696
    | (have j1 := eq16356 (σ y)
       grind)
    | exact resolve eq17696 eq16356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16356 eq17696
  have eq17982 : (σ (M.op x y)) = (k (σ x) (k (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq340 x
       have i₂ := eq14777 y
       grind)
    | exact superpose eq14777 eq340
    | (have j1 := eq14777 y
       grind)
    | exact resolve eq340 eq14777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340 eq14777
  have eq17993 : (σ (M.op x y)) = (k (σ x) (k (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq17982
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17982
    | exact resolve eq17982 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq17982
  have eq18000 : (σ (M.op x y)) = (k (σ x) (k (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq17993
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17993
    | exact resolve eq17993 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17993
  have eq18003 : (σ (M.op x y)) = (k (σ x) (k (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq18000
    | exact resolve eq18000 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18000
  have eq18004 : (σ (M.op x y)) = (k (σ x) (k (σ y) (σ x))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq16173 eq18003
    | exact resolve eq18003 eq16173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18003
  have eq19383 : (k (τ (σ x)) (k y y)) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq15074 eq511
    | (have j1 := eq15074 (σ y)
       grind)
    | exact resolve eq511 eq15074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511 eq15074
  have eq19388 : (τ (M.op (σ x) (σ y))) = (k (τ (σ x)) (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq19383
    | exact resolve eq19383 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19383
  have eq19397 : (k x (k y y)) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq29 eq19388
    | exact resolve eq19388 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq19388
  have eq19398 : (k x (k y x)) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq16509 eq19397
    | exact resolve eq19397 eq16509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16509 eq19397
  have eq19399 : (τ (M.op (σ x) (σ y))) = (k x (k y (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq17645 eq19398
    | exact resolve eq19398 eq17645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17645 eq19398
  have eq19402 : (k (σ x) (σ (k y (σ x)))) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq19399 eq35
    | exact resolve eq35 eq19399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq19399
  have eq19403 : (M.op (σ x) (σ y)) = (k (σ x) (σ (k y (σ x)))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq19402
       have i₂ := eq14 sF4
       grind)
    | exact superpose eq14 eq19402
    | exact resolve eq19402 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19402
  have eq19404 : (M.op (σ x) (σ y)) = (k (σ x) (k (σ y) (σ (σ x)))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq19403
       have i₂ := eq36 sF2
       grind)
    | exact superpose eq36 eq19403
    | exact resolve eq19403 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq19403
  have eq19405 : (M.op (σ x) (σ y)) = (k (σ x) (k (σ y) (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq17703 eq19404
    | exact resolve eq19404 eq17703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17703 eq19404
  have eq19409 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq19405 eq18004
    | exact resolve eq18004 eq19405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19405
  have eq19414 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq19409
       have r₂ := eq27
       grind)
    | exact resolve eq19409 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19409
  have eq19426 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq19414 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) x
       have r₂ := eq19414
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq19414
       grind)
    | exact resolve eq13 eq19414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19414
  have eq19442 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq19426 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19426
  have eq19523 : (M.op (σ x) (σ y)) = (k (σ x) (k (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq19442 eq15075
    | exact resolve eq15075 eq19442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15075 eq19442
  have eq19567 : (M.op (σ x) (σ y)) = (k (σ x) (k (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq19523
    | exact resolve eq19523 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19523
  have eq19592 : (M.op (σ x) (σ y)) = (k (σ x) (k (σ y) (σ x))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq16173 eq19567
    | exact resolve eq19567 eq16173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16173 eq19567
  have eq19612 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq18004 eq19592
    | exact resolve eq19592 eq18004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18004 eq19592
  have eq19626 : y = (M.op y y) := by
    first
    | (have r₁ := eq19612
       have r₂ := eq27
       grind)
    | exact resolve eq19612 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19612
  have eq19638 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq19626
       grind)
    | exact superpose eq19626 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq19626
       grind)
    | exact resolve eq13 eq19626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19654 : ∀ X0 : G, (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq19638 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19638
  have eq19748 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq19654 x
       grind)
    | exact superpose eq19654 eq18
    | (have j1 := eq19654 x
       grind)
    | exact resolve eq18 eq19654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq19749 : y = (k y y) := by
    first
    | (have i₁ := eq19626
       have i₂ := eq19654 y
       grind)
    | exact superpose eq19654 eq19626
    | exact resolve eq19626 eq19654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19626 eq19654
  have eq19835 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq19748
       grind)
    | exact superpose eq19748 eq39
    | exact resolve eq39 eq19748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq19748
  have eq19836 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq19835
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19835
    | exact resolve eq19835 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19835
  have eq19842 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq19836
    | exact resolve eq19836 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq19836
  have eq19858 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1126 y X0
       have i₂ := eq19749
       grind)
    | exact superpose eq19749 eq1126
    | (have j0 := eq1126 y X0
       grind)
    | exact resolve eq1126 eq19749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126 eq19749
  have eq19870 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq19858 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19858
  have eq19875 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19870 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19870
    | (have j0 := eq19870 X0
       grind)
    | exact resolve eq19870 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq19870
  have eq20056 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq19875 eq26
    | (have j1 := eq19875 (σ x)
       grind)
    | exact resolve eq26 eq19875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq19875
  have eq20060 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19842 eq20056
    | exact resolve eq20056 eq19842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19842 eq20056
  have eq20097 : False := by grind
  exact eq20097

/-- `Equation575`: `x = y ◇ (z ◇ (z ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_y_pxy_Equation575 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law575 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law575.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 (M.op X1 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq18
  have eq31 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X1 X0))) = (M.op X1 (M.op X2 (M.op X2 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X3 (M.op X3 (M.op X1 X0))) X1 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq305 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X2 (M.op X0 X1)))) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X0 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X1 X0 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq313 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq301 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq318 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq317 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq320 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq313 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq313 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq313 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq313 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313
  have eq325 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X2 (M.op X0 X1)))) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq305 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq305 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq305 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq329 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq318 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq318 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq318 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq334 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq325 X0 X1 x
       have i₂ := eq9 X1 X0 x
       grind)
    | exact superpose eq9 eq325
    | (have j0 := eq325 X0 X1 x
       grind)
    | exact resolve eq325 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq341 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq334 (σ x) (σ y)
       grind)
    | exact superpose eq334 eq16
    | (have j1 := eq334 (σ x) (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq334 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq334 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq347 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq341
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq341
    | exact resolve eq341 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq348 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq347
       have i₂ := eq334 x y
       grind)
    | exact superpose eq334 eq347
    | (have j1 := eq334 (σ x) (σ y)
       grind)
    | (have r₁ := eq347
       have r₂ := eq334 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq347
       have r₂ := eq334 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq347 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq347
  have eq349 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq348
  have eq351 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq349
       grind)
    | exact superpose eq349 eq10
    | exact resolve eq10 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq368 : x = y ∨ x = y := by
    first
    | (have i₁ := eq351
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq351
    | exact resolve eq351 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq369 : x = y := by grind
  clear eq368
  have eq370 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq369
       grind)
    | exact superpose eq369 eq16
    | exact resolve eq16 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq384 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq185 X0
       have i₂ := eq329 X0 X0
       grind)
    | exact superpose eq329 eq185
    | (have j0 := eq185 X0
       have j1 := eq329 X0 X0
       grind)
    | exact resolve eq185 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq329
  have eq389 : ∀ X0 : G, (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq384 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq453 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq370
       have i₂ := eq14 (σ x) X0
       grind)
    | (have i₁ := eq370
       have i₂ := eq14 (σ x) (σ x)
       grind)
    | exact superpose eq14 eq370
    | (have j1 := eq14 (σ x) X0
       grind)
    | exact resolve eq370 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) X0) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq453 X0
       have j1 := eq12 (σ x) X0
       grind)
    | (have r₁ := eq453 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq453 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq693 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ X0 ∨ (k (σ x) (M.op X1 (M.op X1 (M.op (σ x) X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq457 (M.op x (M.op x (M.op (σ x) X0)))
       have i₂ := eq9 X0 (σ x) x
       grind)
    | exact superpose eq9 eq457
    | (have r₁ := eq457 (M.op x (M.op x (M.op (σ x) (σ (M.op x x)))))
       have r₂ := eq9 (σ (M.op x x)) (σ x) x
       grind)
    | exact resolve eq457 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq719 : ∀ X0 : G, (σ (M.op x x)) = (k (σ x) (M.op X0 (M.op X0 (M.op (σ x) (σ (M.op x x)))))) := by
    intro X0
    first
    | (have j0 := eq693 (σ (M.op x x)) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq740 : ∀ X0 : G, (k x (τ (M.op X0 (M.op X0 (M.op (σ x) (σ (M.op x x))))))) = (τ (σ (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq28 x (M.op X0 (M.op X0 (M.op (σ x) (σ (M.op x x)))))
       have i₂ := eq719 X0
       grind)
    | exact superpose eq719 eq28
    | exact resolve eq28 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq719
  have eq743 : ∀ X0 : G, (M.op x x) = (k x (τ (M.op X0 (M.op X0 (M.op (σ x) (σ (M.op x x))))))) := by
    intro X0
    first
    | (have i₁ := eq740 X0
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq740
    | exact resolve eq740 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq766 : ∀ X0 : G, (M.op x x) = (k x (τ (M.op (σ x) (M.op X0 (M.op X0 (σ (M.op x x))))))) := by
    intro X0
    first
    | (have i₁ := eq743 x
       have i₂ := eq31 (σ (M.op x x)) (σ x) X0 x
       grind)
    | (have i₁ := eq743 (σ x)
       have i₂ := eq31 (σ (M.op x x)) (σ x) (σ x) x
       grind)
    | exact superpose eq31 eq743
    | exact resolve eq743 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq773 : ∀ X0 : G, (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op x (τ (M.op X0 (M.op X0 (M.op (σ x) (σ (M.op x x))))))) := by
    intro X0
    first
    | (have i₁ := eq320 x (τ (M.op X0 (M.op X0 (M.op (σ x) (σ (M.op x x))))))
       have i₂ := eq743 X0
       grind)
    | exact superpose eq743 eq320
    | (have r₁ := eq320 x (τ (M.op X0 (M.op X0 (M.op (σ x) (σ (M.op x x))))))
       have r₂ := eq743 X0
       grind)
    | exact resolve eq320 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320 eq743
  have eq774 : ∀ X0 : G, (M.op x x) = (M.op x (τ (M.op X0 (M.op X0 (M.op (σ x) (σ (M.op x x))))))) := by
    intro X0
    first
    | (have j0 := eq773 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq844 : ∀ X0 X1 : G, (τ (M.op X1 (M.op X1 (M.op (σ x) (σ (M.op x x)))))) = (M.op x (M.op X0 (M.op X0 (M.op x x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ (M.op X1 (M.op X1 (M.op (σ x) (σ (M.op x x)))))) x X0
       have i₂ := eq774 X1
       grind)
    | exact superpose eq774 eq9
    | exact resolve eq9 eq774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq853 : ∀ X1 : G, x = (τ (M.op X1 (M.op X1 (M.op (σ x) (σ (M.op x x)))))) := by
    intro X1
    first
    | (have i₁ := eq844 x X1
       have i₂ := eq9 x x x
       grind)
    | exact superpose eq9 eq844
    | exact resolve eq844 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq878 : (M.op x x) = (k x x) := by
    first
    | (have i₁ := eq766 (σ x)
       have i₂ := eq853 (σ x)
       grind)
    | exact superpose eq853 eq766
    | exact resolve eq766 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq898 : x = (M.op x x) := by
    first
    | (have i₁ := eq878
       have i₂ := eq389 x
       grind)
    | exact superpose eq389 eq878
    | exact resolve eq878 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878
  have eq922 : ∀ X0 : G, x = (τ (M.op X0 (M.op X0 (M.op (σ x) (σ x))))) := by
    intro X0
    first
    | (have i₁ := eq853 X0
       have i₂ := eq898
       grind)
    | exact superpose eq898 eq853
    | exact resolve eq853 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq923 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq898
       grind)
    | exact superpose eq898 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq898
       grind)
    | exact resolve eq12 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq935 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq923 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq1286 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (M.op (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op X0 (M.op X0 (M.op (σ x) (σ x))))
       have i₂ := eq922 X0
       grind)
    | exact superpose eq922 eq11
    | exact resolve eq11 eq922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq2198 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq9 (σ x) (σ x) x
       have i₂ := eq1286 x
       grind)
    | exact superpose eq1286 eq9
    | exact resolve eq9 eq1286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286
  have eq2272 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq370
       have i₂ := eq2198
       grind)
    | exact superpose eq2198 eq370
    | exact resolve eq370 eq2198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370 eq2198
  have eq2301 : (σ x) ≠ (σ (k x x)) := by
    first
    | (have i₁ := eq2272
       have i₂ := eq935 x
       grind)
    | exact superpose eq935 eq2272
    | exact resolve eq2272 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935 eq2272
  have eq2310 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2301
       have i₂ := eq389 x
       grind)
    | exact superpose eq389 eq2301
    | exact resolve eq2301 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389 eq2301
  have eq2311 : False := by grind
  exact eq2311
