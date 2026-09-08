import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pyx_Equation1 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq26 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq30 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq26 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq30
  have eq37 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ X1 = X2 ∨ (k X1 X2) = (M.op X1 X2) ∨ (k X2 X0) = (M.op X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq14 X2 X0
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X2
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq43 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq41
    | (have j0 := eq41 X0 X1
       grind)
    | exact resolve eq41 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq45 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq43
    | (have j0 := eq43 X0 X1
       grind)
    | exact resolve eq43 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq67 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq45 X0 X1
       grind)
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq10
    | (have j1 := eq45 X0 X1
       grind)
    | exact resolve eq10 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq117 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq108 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq108
    | (have j0 := eq108 X0 X1
       grind)
    | exact resolve eq108 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq466 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq467 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq466 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq828 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq467 (τ X0) X1
       grind)
    | exact superpose eq467 eq19
    | (have j1 := eq467 (τ X0) X1
       grind)
    | exact resolve eq19 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq849 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq467 X0 (τ X1)
       grind)
    | exact superpose eq467 eq19
    | (have j1 := eq467 X0 (τ X1)
       grind)
    | exact resolve eq19 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq850 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq467 (σ X0) (σ X1)
       grind)
    | exact superpose eq467 eq15
    | (have j1 := eq467 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq883 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq850 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq850
    | (have j0 := eq850 X0 X1
       grind)
    | exact resolve eq850 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq2306 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ X1 = X2 ∨ (k X1 X2) = (M.op X1 X2) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq117 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq117 X0 X1
       grind)
    | exact superpose eq117 eq13
    | (have j0 := eq13 X1 X2
       have j1 := eq117 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq117 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq117 X0 X1
       grind)
    | exact resolve eq13 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq2551 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ X2) = X1 ∨ (M.op (σ X2) X1) = (k (σ X2) X1) ∨ (k X0 (σ X2)) = (σ (M.op X2 (τ X0))) ∨ (τ X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X2 X1
       have i₂ := eq42 X2 X0
       grind)
    | (have i₁ := eq67 (τ X1) X1
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq67
    | (have j0 := eq67 X2 X1
       have j1 := eq42 X2 X0
       grind)
    | exact resolve eq67 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq67
  have eq2617 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (σ X2) = X1 ∨ (M.op (σ X2) X1) = (k (σ X2) X1) ∨ (k X0 (σ X2)) = (σ (M.op X2 (τ X0))) ∨ (τ X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2551 X0 X1 X2
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq2551
    | (have j0 := eq2551 X0 X1 X2
       grind)
    | (have r₁ := eq2551 X0 X0 X2
       have r₂ := eq31 X0
       grind)
    | exact resolve eq2551 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2551
  have eq56548 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq828 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq828
    | exact resolve eq828 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq56723 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq56548 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq56548
    | (have j0 := eq56548 X0 X1
       grind)
    | exact resolve eq56548 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56548
  have eq67313 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq849 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq849
    | exact resolve eq849 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq67530 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq67313 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq67313
    | (have j0 := eq67313 X0 X1
       grind)
    | exact resolve eq67313 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67313
  have eq99864 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq883 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883
  have eq110927 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq2306 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2306
  have eq113912 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq110927 x y
       grind)
    | exact superpose eq110927 eq16
    | (have j1 := eq110927 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq110927 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq110927 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq110927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110927
  have eq113913 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq56723 x y
       grind)
    | (have r₁ := eq113912
       have r₂ := eq56723 x y
       grind)
    | (have r₁ := eq113912
       have r₂ := eq56723 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq113912
       have r₂ := eq56723 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq113912 eq56723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56723 eq113912
  have eq120011 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2617 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2617
  have eq145485 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op X1 (τ X0)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 (τ X0))
       have i₂ := eq120011 X1 X0
       grind)
    | exact superpose eq120011 eq10
    | (have j1 := eq120011 X1 X0
       grind)
    | exact resolve eq10 eq120011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120011
  have eq145494 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq145485 X0 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq145485
    | (have j0 := eq145485 X0 X1
       grind)
    | exact resolve eq145485 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq145485
  have eq145497 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq145494 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq145494
    | (have j0 := eq145494 (σ X0) X1
       grind)
    | exact resolve eq145494 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145494
  have eq145520 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (k X0 X1) = (M.op X1 X0) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq145497 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq145497
    | (have j0 := eq145497 X0 X1
       grind)
    | exact resolve eq145497 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145497
  have eq145535 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq145520 y x
       grind)
    | exact superpose eq145520 eq16
    | (have j1 := eq145520 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq145520 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq145520 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq145520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145520
  have eq145536 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq67530 y x
       grind)
    | (have r₁ := eq145535
       have r₂ := eq67530 y x
       grind)
    | (have r₁ := eq145535
       have r₂ := eq67530 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq145535
       have r₂ := eq67530 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq145535 eq67530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67530 eq145535
  have eq145566 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq99864 x y
       have i₂ := eq145536
       grind)
    | exact superpose eq145536 eq99864
    | (have j0 := eq99864 x y
       grind)
    | exact resolve eq99864 eq145536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99864 eq145536
  have eq145628 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq145566
  have eq145661 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq145628
       have r₂ := eq16
       grind)
    | exact resolve eq145628 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145628
  have eq145815 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq145661
       have i₂ := eq113913
       grind)
    | exact superpose eq113913 eq145661
    | exact resolve eq145661 eq113913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113913 eq145661
  have eq145834 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq145815
  have eq145835 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq145834
  have eq145859 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq145835
       grind)
    | exact superpose eq145835 eq10
    | exact resolve eq10 eq145835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145835
  have eq146264 : x = y ∨ x = y := by
    first
    | (have i₁ := eq145859
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq145859
    | exact resolve eq145859 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145859
  have eq146265 : x = y := by grind
  clear eq146264
  have eq146288 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq146265
       grind)
    | exact superpose eq146265 eq16
    | exact resolve eq16 eq146265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146265
  have eq146289 : False := by grind
  exact eq146289

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyx_pxy_Equation1 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq26 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq30 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq26 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq30
  have eq37 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ X1 = X2 ∨ (k X1 X2) = (M.op X2 X1) ∨ (k X2 X0) = (M.op X2 X0) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq14 X2 X0
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X2
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ X1 = X2 ∨ (k X1 X2) = (M.op X2 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X2
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq42 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq43 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq41
    | (have j0 := eq41 X0 X1
       grind)
    | exact resolve eq41 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq43
    | (have j0 := eq43 X0 X1
       grind)
    | exact resolve eq43 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq67 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29
    | exact resolve eq29 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq45 X0 X1
       grind)
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq10
    | (have j1 := eq45 X0 X1
       grind)
    | exact resolve eq10 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq117 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq108 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq108
    | (have j0 := eq108 X0 X1
       grind)
    | exact resolve eq108 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq466 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq467 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq466 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq549 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq38 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq550 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq549 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq849 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq467 X1 (τ X0)
       grind)
    | exact superpose eq467 eq19
    | (have j1 := eq467 X1 (τ X0)
       grind)
    | exact resolve eq19 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq850 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq467 (σ X1) (σ X0)
       grind)
    | exact superpose eq467 eq15
    | (have j1 := eq467 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq883 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq850 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq850
    | (have j0 := eq850 X0 X1
       grind)
    | exact resolve eq850 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq1007 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq550 X0 (τ X1)
       grind)
    | exact superpose eq550 eq19
    | (have j1 := eq550 X0 (τ X1)
       grind)
    | exact resolve eq19 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1020 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq550 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2306 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ X1 = X2 ∨ (k X1 X2) = (M.op X2 X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq117 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq117 X0 X1
       grind)
    | exact superpose eq117 eq13
    | (have j0 := eq13 X1 X2
       have j1 := eq117 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq117 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq117 X0 X1
       grind)
    | exact resolve eq13 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq2551 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ X2) = X1 ∨ (M.op X1 (σ X2)) = (k (σ X2) X1) ∨ (k X0 (σ X2)) = (σ (M.op (τ X0) X2)) ∨ (τ X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X2 X1
       have i₂ := eq42 X0 X2
       grind)
    | (have i₁ := eq67 (τ X0) X1
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq67
    | (have j0 := eq67 X2 X1
       have j1 := eq42 X0 X2
       grind)
    | exact resolve eq67 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq67
  have eq2617 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (σ X2) = X1 ∨ (M.op X1 (σ X2)) = (k (σ X2) X1) ∨ (k X0 (σ X2)) = (σ (M.op (τ X0) X2)) ∨ (τ X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2551 X0 X1 X2
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq2551
    | (have j0 := eq2551 X0 X1 X2
       grind)
    | (have r₁ := eq2551 X0 X0 X2
       have r₂ := eq31 X0
       grind)
    | exact resolve eq2551 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2551
  have eq67288 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq849 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq849
    | exact resolve eq849 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq67505 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq67288 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq67288
    | (have j0 := eq67288 X0 X1
       grind)
    | exact resolve eq67288 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67288
  have eq88738 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1007 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1007
    | exact resolve eq1007 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq88766 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq88738 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq88738
    | (have j0 := eq88738 X0 X1
       grind)
    | exact resolve eq88738 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88738
  have eq103310 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq883 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883
  have eq111407 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (k (τ X1) (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq103310 (τ X0) (τ X1)
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq103310
    | (have j0 := eq103310 (τ X0) (τ X1)
       grind)
    | exact resolve eq103310 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq111418 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (k (σ (τ X1)) X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq111407 X0 X1
       have i₂ := eq19 X0 (τ X1)
       grind)
    | exact superpose eq19 eq111407
    | (have j0 := eq111407 X0 X1
       grind)
    | exact resolve eq111407 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq111407
  have eq111426 : ∀ X0 X1 : G, (k X1 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq111418 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq111418
    | (have j0 := eq111418 X0 X1
       grind)
    | exact resolve eq111418 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111418
  have eq111433 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq111426 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq111426
    | (have j0 := eq111426 X0 X1
       grind)
    | (have r₁ := eq111426 X1 X1
       have r₂ := eq11 (k X1 X1)
       grind)
    | exact resolve eq111426 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111426
  have eq111437 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq111433 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq111433
    | (have j0 := eq111433 X0 X1
       grind)
    | exact resolve eq111433 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111433
  have eq111441 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq111437 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq111437
    | (have j0 := eq111437 X0 X1
       grind)
    | exact resolve eq111437 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111437
  have eq111443 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq111441 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq111441
    | (have j0 := eq111441 X0 X1
       grind)
    | exact resolve eq111441 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111441
  have eq111445 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq111443 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq111443
    | (have j0 := eq111443 X0 X1
       grind)
    | exact resolve eq111443 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111443
  have eq111447 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq111445 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq111445
    | (have j0 := eq111445 X0 X1
       grind)
    | exact resolve eq111445 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111445
  have eq111479 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq111447 X0 X1
       have i₂ := eq550 X0 X1
       grind)
    | exact superpose eq550 eq111447
    | (have j0 := eq111447 X0 X1
       have j1 := eq550 X0 X1
       grind)
    | (have r₁ := eq111447 X0 X1
       have r₂ := eq550 (k X0 X1) (k X1 X0)
       grind)
    | (have r₁ := eq111447 X0 X1
       have r₂ := eq550 (k X1 X0) (k X0 X1)
       grind)
    | exact resolve eq111447 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550 eq111447
  have eq111591 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq111479 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111479
  have eq111598 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq111591 X0 X1
       have j1 := eq1020 X0 X1
       grind)
    | (have r₁ := eq111591 X1 X0
       have r₂ := eq1020 X0 X1
       grind)
    | (have r₁ := eq111591 X0 X1
       have r₂ := eq1020 (M.op X0 X1) (k X1 X0)
       grind)
    | (have r₁ := eq111591 X0 X1
       have r₂ := eq1020 (k X1 X0) (M.op X0 X1)
       grind)
    | exact resolve eq111591 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020 eq111591
  have eq114293 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq2306 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2306
  have eq117464 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq114293 x y
       grind)
    | exact superpose eq114293 eq16
    | (have j1 := eq114293 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq114293 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq114293 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq114293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114293
  have eq117465 : (k x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq88766 y x
       grind)
    | (have r₁ := eq117464
       have r₂ := eq88766 y x
       grind)
    | (have r₁ := eq117464
       have r₂ := eq88766 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq117464
       have r₂ := eq88766 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq117464 eq88766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88766 eq117464
  have eq117528 : (M.op y x) ≠ (M.op y x) ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq111598 y x
       have i₂ := eq117465
       grind)
    | exact superpose eq117465 eq111598
    | (have j0 := eq111598 x y
       grind)
    | (have r₁ := eq111598 y x
       have r₂ := eq117465
       grind)
    | exact resolve eq111598 eq117465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111598 eq117465
  have eq117529 : (M.op y x) ≠ (M.op y x) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq117528
  have eq117530 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq117529
  have eq117647 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq103310 x y
       have i₂ := eq117530
       grind)
    | exact superpose eq117530 eq103310
    | (have j0 := eq103310 x y
       grind)
    | exact resolve eq103310 eq117530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103310 eq117530
  have eq117666 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq117647
  have eq117725 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq117666
       have r₂ := eq16
       grind)
    | exact resolve eq117666 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117666
  have eq123427 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2617 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2617
  have eq150690 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) X1)
       have i₂ := eq123427 X1 X0
       grind)
    | exact superpose eq123427 eq10
    | (have j1 := eq123427 X1 X0
       grind)
    | exact resolve eq10 eq123427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123427
  have eq150699 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq150690 X0 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq150690
    | (have j0 := eq150690 X0 X1
       grind)
    | exact resolve eq150690 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq150690
  have eq150715 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq150699 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq150699
    | (have j0 := eq150699 (σ X0) X1
       grind)
    | exact resolve eq150699 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150699
  have eq150738 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq150715 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq150715
    | (have j0 := eq150715 X0 X1
       grind)
    | exact resolve eq150715 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150715
  have eq150804 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq150738 x y
       grind)
    | exact superpose eq150738 eq16
    | (have j1 := eq150738 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq150738 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq150738 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq150738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150738
  have eq150810 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq67505 x y
       grind)
    | (have r₁ := eq150804
       have r₂ := eq67505 x y
       grind)
    | (have r₁ := eq150804
       have r₂ := eq67505 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq150804
       have r₂ := eq67505 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq150804 eq67505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67505 eq150804
  have eq150841 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq117725
       have i₂ := eq150810
       grind)
    | exact superpose eq150810 eq117725
    | exact resolve eq117725 eq150810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117725 eq150810
  have eq150926 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq150841
  have eq150927 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq150926
  have eq150962 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq150927
       grind)
    | exact superpose eq150927 eq10
    | exact resolve eq10 eq150927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150927
  have eq151367 : x = y ∨ x = y := by
    first
    | (have i₁ := eq150962
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq150962
    | exact resolve eq150962 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150962
  have eq151368 : x = y := by grind
  clear eq151367
  have eq151370 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq151368
       grind)
    | exact superpose eq151368 eq16
    | exact resolve eq16 eq151368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151368
  have eq151371 : False := by grind
  exact eq151371

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation1 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq32 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq33 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq68 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq32 x y
       grind)
    | exact superpose eq32 eq16
    | (have j1 := eq32 x y
       grind)
    | exact resolve eq16 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq284 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33
    | exact resolve eq33 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq312 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq284 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq284
    | (have j0 := eq284 X0 X1
       grind)
    | exact resolve eq284 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq660 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq68
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq68
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq68
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq68
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq68 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq661 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq660
  have eq3112 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq661
       grind)
    | exact superpose eq661 eq16
    | exact resolve eq16 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3113 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq661
       grind)
    | exact superpose eq661 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq661
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq661
       grind)
    | exact resolve eq13 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq3114 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq3113
  have eq3115 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq3114
  have eq3117 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3115
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq3115
    | exact resolve eq3115 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3115
  have eq5532 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq312 x y
       have i₂ := eq3117
       grind)
    | exact superpose eq3117 eq312
    | (have j0 := eq312 x y
       grind)
    | exact resolve eq312 eq3117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq5534 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq3117
       grind)
    | exact superpose eq3117 eq10
    | exact resolve eq10 eq3117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3117
  have eq5579 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq5532
  have eq5607 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5534
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5534
    | exact resolve eq5534 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5534
  have eq5608 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5579
       have r₂ := eq3112
       grind)
    | exact resolve eq5579 eq3112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3112 eq5579
  have eq5611 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq5607
       have r₂ := eq13 x y
       grind)
    | exact resolve eq5607 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5607
  have eq5944 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq70 x y
       have i₂ := eq5611
       grind)
    | exact superpose eq5611 eq70
    | (have j0 := eq70 x y
       grind)
    | exact resolve eq70 eq5611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq5611
  have eq5947 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5944
  have eq5948 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5947
  have eq6141 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq5948
       grind)
    | exact superpose eq5948 eq16
    | exact resolve eq16 eq5948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5948
  have eq6342 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6141
       have i₂ := eq5608
       grind)
    | exact superpose eq5608 eq6141
    | exact resolve eq6141 eq5608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5608 eq6141
  have eq6343 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6342
  have eq6344 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq6343
  have eq6504 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6344
       grind)
    | exact superpose eq6344 eq10
    | exact resolve eq10 eq6344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6344
  have eq6583 : x = y ∨ x = y := by
    first
    | (have i₁ := eq6504
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6504
    | exact resolve eq6504 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6504
  have eq6584 : x = y := by grind
  clear eq6583
  have eq6749 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6584
       grind)
    | exact superpose eq6584 eq16
    | exact resolve eq16 eq6584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6584
  have eq6750 : False := by grind
  exact eq6750

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation1 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq32 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq33 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq68 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq32 x y
       grind)
    | exact superpose eq32 eq16
    | (have j1 := eq32 x y
       grind)
    | exact resolve eq16 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq284 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33
    | exact resolve eq33 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq312 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq284 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq284
    | (have j0 := eq284 X0 X1
       grind)
    | exact resolve eq284 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq660 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq68
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq68
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq68
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq68
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq68 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq661 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq660
  have eq3116 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq661
       grind)
    | exact superpose eq661 eq16
    | exact resolve eq16 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3117 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq661
       grind)
    | exact superpose eq661 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq661
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq661
       grind)
    | exact resolve eq13 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq3118 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3117
  have eq3119 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3118
  have eq3121 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3119
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3119
    | exact resolve eq3119 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3119
  have eq5536 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq312 y x
       have i₂ := eq3121
       grind)
    | exact superpose eq3121 eq312
    | (have j0 := eq312 y x
       grind)
    | exact resolve eq312 eq3121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq5538 : (k y x) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq3121
       grind)
    | exact superpose eq3121 eq10
    | exact resolve eq10 eq3121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3121
  have eq5583 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq5536
  have eq5611 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5538
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5538
    | exact resolve eq5538 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5538
  have eq5612 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5583
       have r₂ := eq3116
       grind)
    | exact resolve eq5583 eq3116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3116 eq5583
  have eq5615 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x (k y x)
       grind)
    | (have r₁ := eq5611
       have r₂ := eq13 y x
       grind)
    | exact resolve eq5611 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5611
  have eq5948 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq70 x y
       have i₂ := eq5615
       grind)
    | exact superpose eq5615 eq70
    | (have j0 := eq70 x y
       grind)
    | exact resolve eq70 eq5615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq5615
  have eq5951 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5948
  have eq5952 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5951
  have eq6145 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq5952
       grind)
    | exact superpose eq5952 eq16
    | exact resolve eq16 eq5952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5952
  have eq6346 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6145
       have i₂ := eq5612
       grind)
    | exact superpose eq5612 eq6145
    | exact resolve eq6145 eq5612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5612 eq6145
  have eq6347 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6346
  have eq6348 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq6347
  have eq6508 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6348
       grind)
    | exact superpose eq6348 eq10
    | exact resolve eq10 eq6348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6348
  have eq6587 : x = y ∨ x = y := by
    first
    | (have i₁ := eq6508
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6508
    | exact resolve eq6508 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6508
  have eq6588 : x = y := by grind
  clear eq6587
  have eq6753 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6588
       grind)
    | exact superpose eq6588 eq16
    | exact resolve eq16 eq6588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6588
  have eq6754 : False := by grind
  exact eq6754

/-- `Equation4380`: `x ◇ (x ◇ x) = (x ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pxy_pyy_pyx_Equation4380 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4380 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4380.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq47 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq276 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq272 X0 X1
       have j1 := eq48 X1 X0
       grind)
    | (have r₁ := eq272 X0 X0
       have r₂ := eq48 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq272 X0 X1
       have r₂ := eq48 X0 X1
       grind)
    | (have r₁ := eq272 X1 X0
       have r₂ := eq48 X0 X1
       grind)
    | exact resolve eq272 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq272
  have eq301 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq538 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq301 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq539 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq538 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq621 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq539 (σ X0)
       grind)
    | exact superpose eq539 eq15
    | exact resolve eq15 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq628 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq621 X0
       have i₂ := eq539 X0
       grind)
    | exact superpose eq539 eq621
    | exact resolve eq621 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539 eq621
  have eq1033 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq1042 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq276 X1 (σ X0)
       have i₂ := eq628 X0
       grind)
    | exact superpose eq628 eq276
    | (have j0 := eq276 X1 (σ X0)
       grind)
    | exact resolve eq276 eq628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq1046 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1033 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq1033
    | exact resolve eq1033 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033
  have eq1052 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq1046
  have eq4356 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq1042 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq1042 X0 (σ X0)
       grind)
    | exact superpose eq1042 eq10
    | (have j1 := eq1042 X1 X0
       grind)
    | exact resolve eq10 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq5703 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq4356 (σ X1) X0
       grind)
    | exact superpose eq4356 eq15
    | (have j1 := eq4356 (σ X1) X0
       grind)
    | exact resolve eq15 eq4356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4356
  have eq5729 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5703 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5703
    | (have j0 := eq5703 X0 X1
       grind)
    | exact resolve eq5703 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5703
  have eq7807 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5729 x y
       grind)
    | exact superpose eq5729 eq16
    | (have j1 := eq5729 x y
       grind)
    | exact resolve eq16 eq5729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5729
  have eq8626 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq7807
       have i₂ := eq276 y x
       grind)
    | exact superpose eq276 eq7807
    | (have j1 := eq276 y x
       grind)
    | exact resolve eq7807 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276 eq7807
  have eq8638 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq8626
  have eq8639 : y = (M.op x x) := by grind
  clear eq8638
  have eq9424 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1052 x
       have i₂ := eq8639
       grind)
    | exact superpose eq8639 eq1052
    | exact resolve eq1052 eq8639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052 eq8639
  have eq9436 : False := by grind
  exact eq9436

/-- `Equation4380`: `x ◇ (x ◇ x) = (x ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_x_pyx_Equation4380 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4380 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4380.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq67 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq68 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq14 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq296 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq301 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq296 X0 X1
       have j1 := eq68 X0 X1
       grind)
    | (have r₁ := eq296 X0 X0
       have r₂ := eq68 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq296 X0 X1
       have r₂ := eq68 X0 X1
       grind)
    | (have r₁ := eq296 X1 X0
       have r₂ := eq68 X0 X1
       grind)
    | exact resolve eq296 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq296
  have eq326 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq573 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq326 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq574 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq573 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq658 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq574 (σ X0)
       grind)
    | exact superpose eq574 eq15
    | exact resolve eq15 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq658 X0
       have i₂ := eq574 X0
       grind)
    | exact superpose eq574 eq658
    | exact resolve eq658 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq658
  have eq1194 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq1206 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq301 (σ X0) X1
       have i₂ := eq665 X0
       grind)
    | exact superpose eq665 eq301
    | (have j0 := eq301 (σ X0) X1
       grind)
    | exact resolve eq301 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq1212 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq1194 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq1194
    | exact resolve eq1194 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194
  have eq1219 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq1212
  have eq1221 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1219 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1219
    | exact resolve eq1219 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219
  have eq5669 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq1206 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq1206 X0 (σ X0)
       grind)
    | exact superpose eq1206 eq10
    | (have j1 := eq1206 X1 X0
       grind)
    | exact resolve eq10 eq1206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206
  have eq7822 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq5669 (σ X0) X1
       grind)
    | exact superpose eq5669 eq15
    | (have j1 := eq5669 (σ X0) X1
       grind)
    | exact resolve eq15 eq5669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5669
  have eq7864 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7822 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7822
    | (have j0 := eq7822 X0 X1
       grind)
    | exact resolve eq7822 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7822
  have eq10875 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7864 x y
       grind)
    | exact superpose eq7864 eq16
    | (have j1 := eq7864 x y
       grind)
    | exact resolve eq16 eq7864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7864
  have eq11709 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10875
       have i₂ := eq301 y x
       grind)
    | exact superpose eq301 eq10875
    | (have j1 := eq301 y x
       grind)
    | exact resolve eq10875 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301 eq10875
  have eq11725 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by grind
  clear eq11709
  have eq11726 : x = (M.op y y) := by grind
  clear eq11725
  have eq12271 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq11726
       grind)
    | exact superpose eq11726 eq9
    | exact resolve eq9 eq11726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12288 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq1221 y
       have i₂ := eq11726
       grind)
    | exact superpose eq11726 eq1221
    | exact resolve eq1221 eq11726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221 eq11726
  have eq17004 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12288
       grind)
    | exact superpose eq12288 eq16
    | exact resolve eq16 eq12288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12288
  have eq17015 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq17004
       have i₂ := eq12271
       grind)
    | exact superpose eq12271 eq17004
    | exact resolve eq17004 eq12271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12271 eq17004
  have eq17016 : False := by grind
  exact eq17016

/-- `Equation4380`: `x ◇ (x ◇ x) = (x ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pyx_x_pxy_Equation4380 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4380 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4380.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq66 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq67 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq14 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq299 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq294 X0 X1
       have j1 := eq67 X0 X1
       grind)
    | (have r₁ := eq294 X0 X0
       have r₂ := eq67 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq294 X0 X1
       have r₂ := eq67 X0 X1
       grind)
    | (have r₁ := eq294 X1 X0
       have r₂ := eq67 X0 X1
       grind)
    | exact resolve eq294 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq294
  have eq324 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq842 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq324 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq843 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq842 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq1010 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq843 (σ X0)
       grind)
    | exact superpose eq843 eq15
    | exact resolve eq15 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1017 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1010 X0
       have i₂ := eq843 X0
       grind)
    | exact superpose eq843 eq1010
    | exact resolve eq1010 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843 eq1010
  have eq1411 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq1427 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq299 (σ X0) X1
       have i₂ := eq1017 X0
       grind)
    | exact superpose eq1017 eq299
    | (have j0 := eq299 (σ X0) X1
       grind)
    | exact resolve eq299 eq1017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017
  have eq1433 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq1411 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq1411
    | exact resolve eq1411 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411
  have eq1440 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq1433
  have eq4384 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq1427 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq1427 X0 (σ X0)
       grind)
    | exact superpose eq1427 eq10
    | (have j1 := eq1427 X1 X0
       grind)
    | exact resolve eq10 eq1427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1427
  have eq6040 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq4384 (σ X1) X0
       grind)
    | exact superpose eq4384 eq15
    | (have j1 := eq4384 (σ X1) X0
       grind)
    | exact resolve eq15 eq4384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4384
  have eq6086 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6040 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq6040
    | (have j0 := eq6040 X0 X1
       grind)
    | exact resolve eq6040 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6040
  have eq8615 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6086 x y
       grind)
    | exact superpose eq6086 eq16
    | (have j1 := eq6086 x y
       grind)
    | exact resolve eq16 eq6086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6086
  have eq9313 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8615
       have i₂ := eq299 x y
       grind)
    | exact superpose eq299 eq8615
    | (have j1 := eq299 x y
       grind)
    | exact resolve eq8615 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299 eq8615
  have eq9320 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq9313
  have eq9321 : y = (M.op x x) := by grind
  clear eq9320
  have eq9790 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1440 x
       have i₂ := eq9321
       grind)
    | exact superpose eq9321 eq1440
    | exact resolve eq1440 eq9321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440 eq9321
  have eq9802 : False := by grind
  exact eq9802

/-- `Equation4380`: `x ◇ (x ◇ x) = (x ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pyx_x_pyx_Equation4380 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4380 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4380.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq66 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq79 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq99 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq79 X1 (τ X0)
       grind)
    | exact superpose eq79 eq20
    | (have j1 := eq79 X1 (τ X0)
       grind)
    | exact resolve eq20 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq101 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq79 (σ X1) (σ X0)
       grind)
    | exact superpose eq79 eq15
    | (have j1 := eq79 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  clear eq79
  have eq128 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq108 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq129 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq128 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq167 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq129 (σ X0)
       grind)
    | exact superpose eq129 eq15
    | exact resolve eq15 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq167 X0
       have i₂ := eq129 X0
       grind)
    | exact superpose eq129 eq167
    | exact resolve eq167 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq167
  have eq260 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0)
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq9
    | exact resolve eq9 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq271 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq263 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq263
    | exact resolve eq263 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq275 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq271
  have eq1731 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq99 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq99
    | exact resolve eq99 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq1851 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1731 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1731
    | (have j0 := eq1731 X0 X1
       grind)
    | exact resolve eq1731 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1731
  have eq2936 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq101 X1 X0
       grind)
    | exact superpose eq101 eq10
    | (have j1 := eq101 X1 X0
       grind)
    | exact resolve eq10 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq3048 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2936 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq2936
    | (have j0 := eq2936 X0 X1
       grind)
    | exact resolve eq2936 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq2936
  have eq3142 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3048 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq3048
    | (have j0 := eq3048 X0 X1
       grind)
    | exact resolve eq3048 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3048
  have eq3355 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3142 y x
       grind)
    | exact superpose eq3142 eq16
    | (have j1 := eq3142 y x
       grind)
    | exact resolve eq16 eq3142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3142
  have eq3409 : x = (M.op y y) := by
    first
    | (have j1 := eq1851 x y
       grind)
    | (have r₁ := eq3355
       have r₂ := eq1851 x y
       grind)
    | exact resolve eq3355 eq1851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1851 eq3355
  have eq3640 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq3409
       grind)
    | exact superpose eq3409 eq9
    | exact resolve eq9 eq3409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3654 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq275 y
       have i₂ := eq3409
       grind)
    | exact superpose eq3409 eq275
    | exact resolve eq275 eq3409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq13736 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq260 y
       have i₂ := eq3409
       grind)
    | exact superpose eq3409 eq260
    | exact resolve eq260 eq3409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260 eq3409
  have eq13826 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq13736
       have i₂ := eq3654
       grind)
    | exact superpose eq3654 eq13736
    | exact resolve eq13736 eq3654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3654 eq13736
  have eq13854 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13826
       have i₂ := eq3640
       grind)
    | exact superpose eq3640 eq13826
    | exact resolve eq13826 eq3640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3640 eq13826
  have eq13867 : False := by grind
  exact eq13867
