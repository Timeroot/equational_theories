import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation2164 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq29 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq29
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq736 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op (M.op X0 X0) X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op x x) X1
       have i₂ := eq108 x x x
       grind)
    | exact superpose eq108 eq13
    | (have j0 := eq13 (k (M.op X0 X0) X1) X0
       grind)
    | exact resolve eq13 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1075 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1078 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq1101 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1078 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq1078
    | (have j0 := eq1078 X0 X1
       grind)
    | exact resolve eq1078 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078
  have eq1716 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ X1)) ≠ X0 ∨ (M.op X0 X0) = (σ X1) ∨ (τ X0) = (k (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (M.op X0 X0) X1
       have i₂ := eq736 X0 (σ X1)
       grind)
    | exact superpose eq736 eq28
    | (have j1 := eq736 X0 (σ X1)
       grind)
    | exact resolve eq28 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq736
  have eq3334 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1101 x y
       grind)
    | exact superpose eq1101 eq16
    | (have j1 := eq1101 x y
       grind)
    | exact resolve eq16 eq1101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3358 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1101 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6982 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1075 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1075
    | exact resolve eq1075 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075
  have eq7063 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6982 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq6982
    | (have j0 := eq6982 X0 X1
       grind)
    | exact resolve eq6982 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6982
  have eq12626 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1716 (M.op x x) X1
       have i₂ := eq108 x x x
       grind)
    | exact superpose eq108 eq1716
    | exact resolve eq1716 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1716
  have eq12693 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12626 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq12626
    | (have j0 := eq12626 (σ X1) X0
       grind)
    | exact resolve eq12626 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12695 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12626 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12626
    | (have j0 := eq12626 X1 (τ X0)
       grind)
    | exact resolve eq12626 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12626
  have eq12730 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (τ (k X1 X0)) = (τ (M.op X1 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12695 X0 X1
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq12695
    | (have j0 := eq12695 X0 X1
       grind)
    | exact resolve eq12695 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12695
  have eq12731 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ (σ X0)) X1) ∨ (σ (M.op X0 X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12693 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq12693
    | (have j0 := eq12693 X0 X1
       grind)
    | exact resolve eq12693 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12693
  have eq12733 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = (M.op X0 X0) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12731 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12731
    | (have j0 := eq12731 X0 X1
       grind)
    | exact resolve eq12731 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12731
  have eq12736 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (τ (k (σ X0) X1)) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12730 X0 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq12730
    | (have j0 := eq12730 (τ (k (σ X0) X1)) (τ (σ (M.op X0 X0)))
       grind)
    | exact resolve eq12730 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12730
  have eq12788 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k (σ X0) X1)) ∨ (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12736 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq12736
    | (have j0 := eq12736 X0 X1
       grind)
    | exact resolve eq12736 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12736
  have eq12807 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X0 X0) = (k X0 (τ X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12788 X0 X1
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq12788
    | (have j0 := eq12788 X0 X1
       grind)
    | exact resolve eq12788 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq12788
  have eq13043 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (σ X0) = (σ X1) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12807 X0 (σ X1)
       have i₂ := eq1101 X0 X1
       grind)
    | exact superpose eq1101 eq12807
    | (have j0 := eq12807 X0 (σ X1)
       have j1 := eq1101 X0 X1
       grind)
    | (have r₁ := eq12807 X0 (σ X1)
       have r₂ := eq1101 X0 X1
       grind)
    | exact resolve eq12807 eq1101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101
  have eq13053 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (σ X0) = (σ X1) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq13043 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13043
  have eq13062 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq13053 X0 X1
       have j1 := eq12807 X0 (σ X1)
       grind)
    | (have r₁ := eq13053 X0 X1
       have r₂ := eq12807 (k X0 X1) (σ (M.op X0 X0))
       grind)
    | (have r₁ := eq13053 X0 X1
       have r₂ := eq12807 (M.op X0 X0) (σ (k X0 X1))
       grind)
    | (have r₁ := eq13053 X0 X1
       have r₂ := eq12807 X0 (σ X1)
       grind)
    | exact resolve eq13053 eq12807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12807 eq13053
  have eq13093 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k X0 X1) = (M.op X0 X0) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13062 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq13062
    | (have j0 := eq13062 X0 X1
       grind)
    | exact resolve eq13062 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13062
  have eq13165 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X1)) ∨ (k X0 X1) = (M.op X0 X0) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13093 X0 X1
       have i₂ := eq7063 X1 X0
       grind)
    | exact superpose eq7063 eq13093
    | (have j0 := eq13093 X0 X1
       have j1 := eq7063 X1 X0
       grind)
    | (have r₁ := eq13093 X0 X0
       have r₂ := eq7063 X0 X0
       grind)
    | (have r₁ := eq13093 X0 X1
       have r₂ := eq7063 (σ (k X0 X1)) (σ (M.op X0 X0))
       grind)
    | (have r₁ := eq13093 X0 X1
       have r₂ := eq7063 (σ (M.op X0 X0)) (σ (k X0 X1))
       grind)
    | exact resolve eq13093 eq7063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13093
  have eq13213 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X1)) ∨ (k X0 X1) = (M.op X0 X0) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13165 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq13165 X0 X1
       have r₂ := eq13 (σ (M.op X0 X0)) (σ (M.op X0 X1))
       grind)
    | (have r₁ := eq13165 X0 X1
       have r₂ := eq13 (σ (M.op X0 X1)) (σ (M.op X0 X0))
       grind)
    | (have r₁ := eq13165 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq13165 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13165
  have eq13574 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq3334
       have i₂ := eq7063 y x
       grind)
    | exact superpose eq7063 eq3334
    | (have j1 := eq7063 y x
       grind)
    | (have r₁ := eq3334
       have r₂ := eq7063 y x
       grind)
    | (have r₁ := eq3334
       have r₂ := eq7063 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq3334
       have r₂ := eq7063 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3334 eq7063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3334 eq7063
  have eq13575 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq13574
  have eq19458 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3358 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq3358
    | (have j0 := eq3358 (τ X0) (τ X1)
       grind)
    | exact resolve eq3358 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq19545 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19458 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq19458
    | (have j0 := eq19458 X0 X1
       grind)
    | exact resolve eq19458 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19458
  have eq19604 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19545 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq19545
    | (have j0 := eq19545 X0 X1
       grind)
    | exact resolve eq19545 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19545
  have eq19650 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19604 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq19604
    | (have j0 := eq19604 X0 X1
       grind)
    | exact resolve eq19604 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19604
  have eq19683 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19650 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19650
    | (have j0 := eq19650 X0 X1
       grind)
    | exact resolve eq19650 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19650
  have eq19707 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19683 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq19683
    | (have j0 := eq19683 X0 X1
       grind)
    | exact resolve eq19683 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq19683
  have eq19726 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19707 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq19707
    | (have j0 := eq19707 X0 X1
       grind)
    | exact resolve eq19707 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19707
  have eq19740 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19726 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19726
    | (have j0 := eq19726 X0 X1
       grind)
    | exact resolve eq19726 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19726
  have eq113829 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13575
       grind)
    | exact superpose eq13575 eq16
    | exact resolve eq16 eq13575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13575
  have eq113830 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq113829
       have r₂ := eq22 x
       grind)
    | exact resolve eq113829 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113829
  have eq113850 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13213 x y
       have i₂ := eq113830
       grind)
    | exact superpose eq113830 eq13213
    | (have j0 := eq13213 x y
       grind)
    | exact resolve eq13213 eq113830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13213 eq113830
  have eq113891 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq113850
  have eq113892 : (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq113891
  have eq113909 : x = y ∨ (σ x) = (σ y) ∨ (k x y) = (M.op x x) := by
    first
    | (have j1 := eq12733 x y
       grind)
    | (have r₁ := eq113892
       have r₂ := eq12733 x y
       grind)
    | exact resolve eq113892 eq12733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12733 eq113892
  have eq113930 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq113909
       grind)
    | exact superpose eq113909 eq16
    | exact resolve eq16 eq113909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113909
  have eq113931 : (k x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq113930
       have r₂ := eq22 x
       grind)
    | exact resolve eq113930 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113930
  have eq113938 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3358 x y
       have i₂ := eq113931
       grind)
    | exact superpose eq113931 eq3358
    | (have j0 := eq3358 x y
       grind)
    | exact resolve eq3358 eq113931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3358
  have eq113959 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19740 x y
       have i₂ := eq113931
       grind)
    | exact superpose eq113931 eq19740
    | (have j0 := eq19740 x y
       grind)
    | (have r₁ := eq19740 x y
       have r₂ := eq113931
       grind)
    | exact resolve eq19740 eq113931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19740 eq113931
  have eq113970 : x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq113959
  have eq113972 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq113938
  have eq113973 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq113972
  have eq113984 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq113970
       grind)
    | exact superpose eq113970 eq16
    | exact resolve eq16 eq113970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113970
  have eq113985 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq113984
       have r₂ := eq22 x
       grind)
    | exact resolve eq113984 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113984
  have eq113990 : ∀ X0 : G, (σ x) = (σ y) ∨ y = (M.op (M.op x x) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq108 x y X0
       have i₂ := eq113985
       grind)
    | exact superpose eq113985 eq108
    | exact resolve eq108 eq113985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq113985
  have eq114064 : ∀ X0 : G, y = (τ (σ x)) ∨ y = (M.op (M.op x x) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq113990 X0
       grind)
    | exact superpose eq113990 eq10
    | (have j1 := eq113990 X0
       grind)
    | exact resolve eq10 eq113990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113990
  have eq114290 : ∀ X0 : G, x = y ∨ y = (M.op (M.op x x) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq114064 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq114064
    | (have j0 := eq114064 X0
       grind)
    | exact resolve eq114064 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114064
  have eq114292 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op (M.op x x) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq114290 X0
       grind)
    | exact superpose eq114290 eq16
    | (have j1 := eq114290 X0
       grind)
    | exact resolve eq16 eq114290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114290
  have eq114293 : ∀ X0 : G, y = (M.op (M.op x x) (M.op y X0)) := by
    intro X0
    first
    | (have j0 := eq114292 X0
       grind)
    | (have r₁ := eq114292 X0
       have r₂ := eq22 x
       grind)
    | exact resolve eq114292 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114292
  have eq114345 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq109 x x (M.op y x)
       have i₂ := eq114293 x
       grind)
    | exact superpose eq114293 eq109
    | exact resolve eq109 eq114293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq114293
  have eq114872 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq113973
       grind)
    | exact superpose eq113973 eq16
    | exact resolve eq16 eq113973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113973
  have eq115071 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq114872
       have i₂ := eq114345
       grind)
    | exact superpose eq114345 eq114872
    | exact resolve eq114872 eq114345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114872
  have eq115072 : (σ x) = (σ y) := by grind
  clear eq115071
  have eq115109 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq115072
       grind)
    | exact superpose eq115072 eq16
    | exact resolve eq16 eq115072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115072
  have eq115337 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq115109
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq115109
    | exact resolve eq115109 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq115109
  have eq115338 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq115337
       have i₂ := eq114345
       grind)
    | exact superpose eq114345 eq115337
    | exact resolve eq115337 eq114345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114345 eq115337
  have eq115339 : False := by grind
  exact eq115339

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyy_pxy_Equation2164 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq18
  have eq32 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq32
  have eq48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq78 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq10
    | exact resolve eq10 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq159 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq160 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq159 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq159
    | (have j0 := eq159 X0 X1
       grind)
    | exact resolve eq159 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq169 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq160 x y
       grind)
    | exact superpose eq160 eq16
    | (have j1 := eq160 x y
       grind)
    | exact resolve eq16 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq191 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op X1 (τ X0)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0) (τ X0)
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq24
    | exact resolve eq24 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq280 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (M.op X1 (τ (M.op X0 X0))) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq191 (M.op X0 X0) X1
       have i₂ := eq24 X0 X0 X0
       grind)
    | exact superpose eq24 eq191
    | exact resolve eq191 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq522 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (M.op (M.op X1 (τ (M.op (σ X0) (σ X0)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq280 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq280
    | exact resolve eq280 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq540 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (M.op (M.op X1 (τ (σ (M.op X0 X0)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq522 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq522
    | exact resolve eq522 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq546 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq540 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq540
    | exact resolve eq540 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq997 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq169
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq169
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq169
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq169
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq169 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq998 : x = y ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq997
  have eq6418 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq998
       grind)
    | exact superpose eq998 eq16
    | exact resolve eq16 eq998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq6419 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq6418
       have r₂ := eq22 x
       grind)
    | exact resolve eq6418 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6418
  have eq11700 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq24 X0 y y
       have i₂ := eq6419
       grind)
    | exact superpose eq6419 eq24
    | exact resolve eq24 eq6419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11701 : ∀ X0 : G, y = (M.op (M.op x x) (M.op y X0)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq24 y y X0
       have i₂ := eq6419
       grind)
    | exact superpose eq6419 eq24
    | exact resolve eq24 eq6419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6419
  have eq27742 : (M.op x x) = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq546 x (M.op x y)
       have i₂ := eq11700 x
       grind)
    | exact superpose eq11700 eq546
    | exact resolve eq546 eq11700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546 eq11700
  have eq27785 : y = (M.op (M.op x x) (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq11701 x
       have i₂ := eq27742
       grind)
    | exact superpose eq27742 eq11701
    | exact resolve eq11701 eq27742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11701 eq27742
  have eq27814 : y = (M.op (M.op x x) (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq27785
  have eq27818 : x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq27814
       have i₂ := eq24 x x x
       grind)
    | (have i₁ := eq27814
       have i₂ := eq24 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq24 eq27814
    | exact resolve eq27814 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27814
  have eq28141 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27818
       grind)
    | exact superpose eq27818 eq16
    | exact resolve eq16 eq27818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27818
  have eq28142 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq28141
       have r₂ := eq22 x
       grind)
    | exact resolve eq28141 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28141
  have eq28469 : (σ (M.op y y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq22 y
       have i₂ := eq28142
       grind)
    | exact superpose eq28142 eq22
    | exact resolve eq22 eq28142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28142
  have eq28601 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq28469
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq28469
    | exact resolve eq28469 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28469
  have eq28602 : (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq28601
  have eq28973 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq22 (M.op y y)
       have i₂ := eq28602
       grind)
    | exact superpose eq28602 eq22
    | exact resolve eq22 eq28602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28602
  have eq29169 : (σ (M.op (M.op y y) (M.op y y))) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq28973
       have i₂ := eq22 (M.op x x)
       grind)
    | exact superpose eq22 eq28973
    | exact resolve eq28973 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28973
  have eq29176 : (σ x) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq29169
       have i₂ := eq24 x x x
       grind)
    | (have i₁ := eq29169
       have i₂ := eq24 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq24 eq29169
    | exact resolve eq29169 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29169
  have eq29177 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq29176
       have i₂ := eq24 y y y
       grind)
    | (have i₁ := eq29176
       have i₂ := eq24 x (M.op (M.op y y) (M.op y y)) x
       grind)
    | exact superpose eq24 eq29176
    | exact resolve eq29176 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq29176
  have eq29528 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq29177
       grind)
    | exact superpose eq29177 eq10
    | exact resolve eq10 eq29177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29177
  have eq29729 : x = y := by
    first
    | (have i₁ := eq29528
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq29528
    | exact resolve eq29528 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29528
  have eq30096 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29729
       grind)
    | exact superpose eq29729 eq16
    | exact resolve eq16 eq29729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29729
  have eq30097 : False := by grind
  exact eq30097

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation2164 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq91 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq287 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq91 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq13
    | (have j0 := eq13 (k (σ X0) (σ X1)) (M.op (σ X0) (σ X1))
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq295 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq287 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq296 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq295 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq303 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq296 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq296
    | (have j0 := eq296 X0 X1
       grind)
    | exact resolve eq296 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq304 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq303 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq758 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq304 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq304
    | exact resolve eq304 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq764 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq304 x y
       grind)
    | exact superpose eq304 eq16
    | (have j1 := eq304 x y
       grind)
    | exact resolve eq16 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq791 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq758 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq758
    | (have j0 := eq758 X0 X1
       grind)
    | exact resolve eq758 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq758
  have eq796 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq791 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq791
    | exact resolve eq791 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791
  have eq983 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq764
       have i₂ := eq796 x y
       grind)
    | exact superpose eq796 eq764
    | (have j1 := eq796 (σ x) (σ y)
       grind)
    | (have r₁ := eq764
       have r₂ := eq796 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq764
       have r₂ := eq796 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq764 eq796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764 eq796
  have eq986 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq983
  have eq988 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq986
       grind)
    | exact superpose eq986 eq10
    | exact resolve eq10 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq1026 : x = y ∨ x = y := by
    first
    | (have i₁ := eq988
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq988
    | exact resolve eq988 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq1027 : x = y := by grind
  clear eq1026
  have eq1072 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1027
       grind)
    | exact superpose eq1027 eq16
    | exact resolve eq16 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027
  have eq1073 : False := by grind
  exact eq1073

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxy_pxx_pxy_Equation2164 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq42 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq280 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op X2 (σ X1)) (M.op (σ X0) (σ X1))) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42 X2 (σ X1) (σ X0)
       have i₂ := eq91 X1 X0
       grind)
    | (have i₁ := eq42 X0 (σ X1) (σ X0)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq42
    | (have j1 := eq91 X1 X0
       grind)
    | exact resolve eq42 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ X0) (σ X1)) (M.op (σ X0) X2)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42 (σ X1) (σ X0) X2
       have i₂ := eq91 X1 X0
       grind)
    | (have i₁ := eq42 (σ X1) (σ X0) x
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq42
    | (have j1 := eq91 X1 X0
       grind)
    | exact resolve eq42 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq91
  have eq2482 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq280 X0 X1 (σ X0)
       have i₂ := eq281 X0 X1 (σ X1)
       grind)
    | exact superpose eq281 eq280
    | (have j0 := eq280 X0 X1 x
       have j1 := eq281 X0 X1 x
       grind)
    | exact resolve eq280 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280 eq281
  have eq2520 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq2482 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2482
  have eq2553 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2520 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2520
    | exact resolve eq2520 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2565 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2520 y x
       grind)
    | exact superpose eq2520 eq16
    | (have j1 := eq2520 x y
       grind)
    | exact resolve eq16 eq2520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2520
  have eq2606 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2553 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq2553
    | (have j0 := eq2553 X0 X1
       grind)
    | exact resolve eq2553 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq2553
  have eq2613 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2606 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2606
    | exact resolve eq2606 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2606
  have eq2889 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2565
       have i₂ := eq2613 x y
       grind)
    | exact superpose eq2613 eq2565
    | (have j1 := eq2613 (σ x) (σ y)
       grind)
    | (have r₁ := eq2565
       have r₂ := eq2613 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2565
       have r₂ := eq2613 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2565 eq2613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2565 eq2613
  have eq2894 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2889
  have eq2896 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2894
       grind)
    | exact superpose eq2894 eq10
    | exact resolve eq10 eq2894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2894
  have eq2962 : x = y ∨ x = y := by
    first
    | (have i₁ := eq2896
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2896
    | exact resolve eq2896 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2896
  have eq2963 : x = y := by grind
  clear eq2962
  have eq3107 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2963
       grind)
    | exact superpose eq2963 eq16
    | exact resolve eq16 eq2963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2963
  have eq3108 : False := by grind
  exact eq3108

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation2164 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq32 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq32
  have eq35 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 (M.op (M.op X0 X1) (M.op X0 X1))) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X2 ∨ (M.op X0 X1) = (k X2 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op X1 X2) (M.op X1 X2))
       have i₂ := eq9 (M.op X1 X2) X1 X2 (M.op X1 X2)
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op (M.op X0 X1) (M.op X0 X1)) X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq52 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31
    | exact resolve eq31 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq78 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq10
    | exact resolve eq10 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq167 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq158 x y
       grind)
    | exact superpose eq158 eq16
    | (have j1 := eq158 x y
       grind)
    | exact resolve eq16 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq158 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq192 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op X1 (τ X0)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0) (τ X0)
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq24
    | exact resolve eq24 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq232 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = (k X0 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1 X0
       have i₂ := eq25 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq25 eq35
    | (have j0 := eq35 X0 X1 X0
       grind)
    | (have r₁ := eq35 X0 x X0
       have r₂ := eq25 X0 x (M.op X0 x)
       grind)
    | exact resolve eq35 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq35
  have eq238 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op (M.op X0 X1) (M.op X0 X1))) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq232 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq295 : ∀ X0 X1 X2 : G, (M.op X2 (τ X0)) = (M.op (M.op X1 (M.op X2 (τ X0))) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 (M.op X2 (τ X0)) (τ (M.op X0 X0))
       have i₂ := eq192 X0 X2
       grind)
    | exact superpose eq192 eq24
    | exact resolve eq24 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq707 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X1 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq295 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq295
    | exact resolve eq295 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq866 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq167
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq167
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq167
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq167
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq167 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq867 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq866
  have eq1788 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (M.op (σ X0) X1)) ∨ (τ (M.op (σ X0) X1)) = (k X0 (τ (M.op (M.op (σ X0) X1) (M.op (σ X0) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 (M.op (M.op (σ X0) X1) (M.op (σ X0) X1))
       have i₂ := eq238 (σ X0) X1
       grind)
    | exact superpose eq238 eq43
    | (have j1 := eq238 (σ X0) X1
       grind)
    | exact resolve eq43 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq1897 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq176 (τ X0) (τ X1)
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq176
    | (have j0 := eq176 (τ X0) (τ X1)
       grind)
    | exact resolve eq176 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq176
  have eq1931 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1897 X0 X1
       have i₂ := eq33 X1
       grind)
    | exact superpose eq33 eq1897
    | (have j0 := eq1897 X0 X1
       grind)
    | exact resolve eq1897 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1897
  have eq1948 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1931 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1931
    | (have j0 := eq1931 X0 X1
       grind)
    | exact resolve eq1931 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1931
  have eq1959 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1948 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1948
    | (have j0 := eq1948 X0 X1
       grind)
    | exact resolve eq1948 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1948
  have eq1966 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1959 X0 X1
       have i₂ := eq33 X1
       grind)
    | exact superpose eq33 eq1959
    | (have j0 := eq1959 X0 X1
       grind)
    | exact resolve eq1959 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq1959
  have eq1972 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1966 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1966
    | (have j0 := eq1966 X0 X1
       grind)
    | exact resolve eq1966 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1966
  have eq1977 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1972 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1972
    | (have j0 := eq1972 X0 X1
       grind)
    | exact resolve eq1972 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1972
  have eq1982 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1977 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1977
    | (have j0 := eq1977 X0 X1
       grind)
    | exact resolve eq1977 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1977
  have eq8398 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq867
       grind)
    | exact superpose eq867 eq16
    | exact resolve eq16 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq8399 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8398
       have r₂ := eq22 x
       grind)
    | exact resolve eq8398 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8398
  have eq21572 : (σ x) = (M.op (σ (M.op y y)) (σ (M.op y y))) ∨ (τ (σ (M.op y y))) = (k x (τ (M.op (σ (M.op y y)) (σ (M.op y y))))) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1788 x (σ y)
       have i₂ := eq8399
       grind)
    | exact superpose eq8399 eq1788
    | exact resolve eq1788 eq8399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1788 eq8399
  have eq21616 : (σ x) = (σ (M.op (M.op y y) (M.op y y))) ∨ (τ (σ (M.op y y))) = (k x (τ (M.op (σ (M.op y y)) (σ (M.op y y))))) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq21572
       have i₂ := eq22 (M.op y y)
       grind)
    | exact superpose eq22 eq21572
    | exact resolve eq21572 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21572
  have eq21622 : (σ x) = (σ y) ∨ (τ (σ (M.op y y))) = (k x (τ (M.op (σ (M.op y y)) (σ (M.op y y))))) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq21616
       have i₂ := eq24 y y y
       grind)
    | (have i₁ := eq21616
       have i₂ := eq24 x (M.op (M.op y y) (M.op y y)) x
       grind)
    | exact superpose eq24 eq21616
    | exact resolve eq21616 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21616
  have eq21623 : (σ x) = (σ y) ∨ (τ (σ (M.op y y))) = (k x (τ (M.op (σ (M.op y y)) (σ (M.op y y))))) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq21622
  have eq21626 : (τ (σ (M.op y y))) = (k x (τ (σ (M.op (M.op y y) (M.op y y))))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq21623
       have i₂ := eq22 (M.op y y)
       grind)
    | exact superpose eq22 eq21623
    | exact resolve eq21623 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21623
  have eq21629 : (τ (σ (M.op y y))) = (k x (M.op (M.op y y) (M.op y y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq21626
       have i₂ := eq10 (M.op (M.op y y) (M.op y y))
       grind)
    | exact superpose eq10 eq21626
    | exact resolve eq21626 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21626
  have eq21633 : (k x y) = (τ (σ (M.op y y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq21629
       have i₂ := eq24 y y y
       grind)
    | (have i₁ := eq21629
       have i₂ := eq24 x (M.op (M.op y y) (M.op y y)) x
       grind)
    | exact superpose eq24 eq21629
    | exact resolve eq21629 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21629
  have eq21635 : (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq21633
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq21633
    | exact resolve eq21633 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21633
  have eq21942 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq1982 x y
       have i₂ := eq21635
       grind)
    | exact superpose eq21635 eq1982
    | (have j0 := eq1982 x y
       grind)
    | (have r₁ := eq1982 x y
       have r₂ := eq21635
       grind)
    | exact resolve eq1982 eq21635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1982 eq21635
  have eq21959 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq21942
  have eq21960 : x = y ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq21959
  have eq22248 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21960
       grind)
    | exact superpose eq21960 eq16
    | exact resolve eq16 eq21960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21960
  have eq22249 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq22248
       have r₂ := eq22 x
       grind)
    | exact resolve eq22248 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22248
  have eq22604 : ∀ X0 : G, (σ x) = (σ y) ∨ y = (M.op (M.op X0 y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq24 X0 y y
       have i₂ := eq22249
       grind)
    | exact superpose eq22249 eq24
    | exact resolve eq24 eq22249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq22249
  have eq22896 : ∀ X0 : G, y = (τ (σ x)) ∨ y = (M.op (M.op X0 y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq22604 X0
       grind)
    | exact superpose eq22604 eq10
    | (have j1 := eq22604 X0
       grind)
    | exact resolve eq10 eq22604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22604
  have eq23012 : ∀ X0 : G, x = y ∨ y = (M.op (M.op X0 y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq22896 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22896
    | (have j0 := eq22896 X0
       grind)
    | exact resolve eq22896 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22896
  have eq23321 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op (M.op X0 y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq23012 X0
       grind)
    | exact superpose eq23012 eq16
    | (have j1 := eq23012 X0
       grind)
    | exact resolve eq16 eq23012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23012
  have eq23322 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq23321 X0
       grind)
    | (have r₁ := eq23321 X0
       have r₂ := eq22 x
       grind)
    | exact resolve eq23321 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23321
  have eq23612 : x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq238 x y
       have i₂ := eq23322 x
       grind)
    | exact superpose eq23322 eq238
    | exact resolve eq238 eq23322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq23618 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq707 y x (M.op x y)
       have i₂ := eq23322 x
       grind)
    | exact superpose eq23322 eq707
    | exact resolve eq707 eq23322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707 eq23322
  have eq24384 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23612
       grind)
    | exact superpose eq23612 eq16
    | exact resolve eq16 eq23612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23612
  have eq24386 : (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq24384
       have r₂ := eq22 x
       grind)
    | exact resolve eq24384 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24384
  have eq24393 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq167
       have i₂ := eq24386
       grind)
    | exact superpose eq24386 eq167
    | exact resolve eq167 eq24386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167 eq24386
  have eq24408 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by grind
  clear eq24393
  have eq24418 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq24408
       have i₂ := eq23618
       grind)
    | exact superpose eq23618 eq24408
    | exact resolve eq24408 eq23618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23618 eq24408
  have eq24424 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq24418
       have r₂ := eq16
       grind)
    | exact resolve eq24418 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24418
  have eq24430 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24424
       grind)
    | exact superpose eq24424 eq10
    | exact resolve eq10 eq24424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24424
  have eq24581 : x = y := by
    first
    | (have i₁ := eq24430
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq24430
    | exact resolve eq24430 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24430
  have eq24592 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24581
       grind)
    | exact superpose eq24581 eq16
    | exact resolve eq16 eq24581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24581
  have eq24595 : False := by grind
  exact eq24595

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_pyy_pxy_Equation2164 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq24 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq30 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq24 X2 X0 x
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq37 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq64 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq28
    | (have j0 := eq28 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq28
    | (have j0 := eq28 (σ X0) (σ X1)
       grind)
    | exact resolve eq28 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq86 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq37
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq141 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X2 (M.op X0 X1)) = X1 ∨ (M.op X1 X1) = (k (M.op X2 (M.op X0 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X2 (M.op X0 X1)) X1
       have i₂ := eq30 X1 X2 X0
       grind)
    | exact superpose eq30 eq13
    | (have j0 := eq13 (M.op X2 (M.op X0 X1)) X1
       grind)
    | exact resolve eq13 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq415 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq34
    | exact resolve eq34 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq429 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq415 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq415
    | (have j0 := eq415 X0 X1
       grind)
    | exact resolve eq415 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq755 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq64 x y
       grind)
    | exact superpose eq64 eq16
    | (have j1 := eq64 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq64 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq64 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq64 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq773 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq755
  have eq803 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq773
       grind)
    | exact superpose eq773 eq16
    | exact resolve eq16 eq773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq807 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq30 (σ y) x (σ x)
       have i₂ := eq773
       grind)
    | exact superpose eq773 eq30
    | exact resolve eq30 eq773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq811 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq773
       grind)
    | exact superpose eq773 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq773
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq773
       grind)
    | exact resolve eq13 eq773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq812 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq811
  have eq813 : (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq812
  have eq815 : (M.op (σ y) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq813
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq813
    | exact resolve eq813 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813
  have eq817 : (σ (M.op y y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq815
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq815
    | exact resolve eq815 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq857 : ∀ X0 X1 : G, (σ (σ X1)) ≠ (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq3682 : (σ (M.op x y)) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq429 x y
       have i₂ := eq817
       grind)
    | exact superpose eq817 eq429
    | (have j0 := eq429 x y
       grind)
    | exact resolve eq429 eq817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429 eq817
  have eq3712 : (σ (M.op x y)) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq3682
  have eq7566 : ∀ X0 X1 : G, (σ (σ (τ X1))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq857 (τ X0) (τ X1)
       have i₂ := eq86 X1 X0
       grind)
    | exact superpose eq86 eq857
    | (have j0 := eq857 (τ X0) (τ X1)
       grind)
    | exact resolve eq857 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq857
  have eq7639 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X1))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7566 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq7566
    | (have j0 := eq7566 X0 X1
       grind)
    | exact resolve eq7566 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7566
  have eq7682 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7639 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7639
    | (have j0 := eq7639 X0 X1
       grind)
    | exact resolve eq7639 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7639
  have eq7715 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (σ (τ X0))) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7682 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7682
    | (have j0 := eq7682 X0 X1
       grind)
    | exact resolve eq7682 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7682
  have eq7739 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7715 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7715
    | (have j0 := eq7715 X0 X1
       grind)
    | exact resolve eq7715 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7715
  have eq7759 : ∀ X0 X1 : G, (σ X1) = (σ (σ (τ X0))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7739 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7739
    | (have j0 := eq7739 X0 X1
       grind)
    | exact resolve eq7739 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7739
  have eq7776 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7759 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7759
    | (have j0 := eq7759 X0 X1
       grind)
    | exact resolve eq7759 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7759
  have eq32601 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq807 (σ x)
       have i₂ := eq773
       grind)
    | exact superpose eq773 eq807
    | exact resolve eq807 eq773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773 eq807
  have eq32617 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq32601
  have eq32622 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq32617
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq32617
    | exact resolve eq32617 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32617
  have eq38608 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3712
       have i₂ := eq32622
       grind)
    | exact superpose eq32622 eq3712
    | exact resolve eq3712 eq32622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3712 eq32622
  have eq38810 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq38608
  have eq38852 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq38810
       have r₂ := eq803
       grind)
    | exact resolve eq38810 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803 eq38810
  have eq45509 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq24 X0 x y
       have i₂ := eq38852
       grind)
    | exact superpose eq38852 eq24
    | exact resolve eq24 eq38852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45510 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq24 x y X0
       have i₂ := eq38852
       grind)
    | exact superpose eq38852 eq24
    | exact resolve eq24 eq38852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq62825 : y = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45510 (M.op y x)
       have i₂ := eq45510 x
       grind)
    | exact superpose eq45510 eq45510
    | exact resolve eq45510 eq45510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45510
  have eq62853 : y = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq62825
  have eq74377 : ∀ X0 : G, y ≠ y ∨ y = (M.op X0 y) ∨ y = (k (M.op X0 y) y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq141 y y x
       have i₂ := eq62853
       grind)
    | exact superpose eq62853 eq141
    | (have r₁ := eq141 y y x
       have r₂ := eq62853
       grind)
    | exact resolve eq141 eq62853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq62853
  have eq74378 : ∀ X0 : G, y = (k (M.op X0 y) y) ∨ y = (M.op X0 y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq74377 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74377
  have eq765409 : y = (k x y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq74378 (M.op x x)
       have i₂ := eq45509 x
       grind)
    | exact superpose eq45509 eq74378
    | exact resolve eq74378 eq45509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45509 eq74378
  have eq765684 : y = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq765409
  have eq793641 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq7776 x y
       have i₂ := eq765684
       grind)
    | exact superpose eq765684 eq7776
    | (have j0 := eq7776 x y
       grind)
    | exact resolve eq7776 eq765684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7776 eq765684
  have eq793719 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq793641
  have eq793720 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq793719
  have eq814711 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq793720
       grind)
    | exact superpose eq793720 eq16
    | exact resolve eq16 eq793720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793720
  have eq841398 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq814711
       have i₂ := eq38852
       grind)
    | exact superpose eq38852 eq814711
    | exact resolve eq814711 eq38852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38852 eq814711
  have eq841399 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq841398
  have eq841400 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq841399
  have eq868460 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq841400
       grind)
    | exact superpose eq841400 eq10
    | exact resolve eq10 eq841400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841400
  have eq869833 : x = y ∨ x = y := by
    first
    | (have i₁ := eq868460
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq868460
    | exact resolve eq868460 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868460
  have eq869834 : x = y := by grind
  clear eq869833
  have eq910294 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq869834
       grind)
    | exact superpose eq869834 eq16
    | exact resolve eq16 eq869834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869834
  have eq910295 : False := by grind
  exact eq910295

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pyx_pxx_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq31 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15
    | (have j0 := eq15 X0 y
       grind)
    | exact resolve eq15 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq50 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9
    | (have j0 := eq9 X0 x y
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9
    | (have j0 := eq9 y x X0
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq9
    | (have j0 := eq9 (σ y) (σ x) X0
       grind)
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq31 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq31
    | (have j0 := eq31 x
       grind)
    | exact resolve eq31 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq72 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq83 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op x y) X0) X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq90 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op x X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq56 eq9
    | exact resolve eq9 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq58
    | (have j0 := eq58 (σ y)
       grind)
    | exact resolve eq58 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ y)) X1) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq58 eq9
    | exact resolve eq9 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq10
    | exact resolve eq10 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq173 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq134 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq134
    | exact resolve eq134 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq200 : ∀ X0 : G, (k (τ (M.op X0 X0)) (τ X0)) = (τ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  have eq304 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op (M.op X1 X0) X2)) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq83 eq9
    | exact resolve eq9 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq322 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq342 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq50 X0 (τ X0)
       have i₂ := eq100 (τ X0)
       grind)
    | exact superpose eq100 eq50
    | (have j1 := eq100 (τ X0)
       grind)
    | exact resolve eq50 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) (τ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq173 X0 X0
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq173
    | (have j1 := eq100 X0
       grind)
    | exact resolve eq173 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq61
       have i₂ := eq100 sF2
       grind)
    | exact superpose eq100 eq61
    | (have j1 := eq100 (σ x)
       grind)
    | exact resolve eq61 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq347 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq100 sF3
       grind)
    | exact superpose eq100 eq72
    | (have j1 := eq100 (σ y)
       grind)
    | exact resolve eq72 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq348 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq342 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq342
    | (have j0 := eq342 X0
       grind)
    | exact resolve eq342 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq553 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 X1) X3) (M.op X1 X3)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 X3 X1 (M.op (M.op X0 x) (M.op X0 X1))
       have i₂ := eq55 X1 X0 x
       grind)
    | exact superpose eq55 eq9
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq90 (M.op (M.op X0 x) (M.op X0 x))
       have i₂ := eq55 x X0 x
       grind)
    | exact superpose eq55 eq90
    | exact resolve eq90 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq626 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1 x (M.op X1 X0)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq57
    | exact resolve eq57 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq663 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X2 (M.op X0 X1) (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have i₂ := eq57 (M.op (M.op X0 X1) X2) X0 X1 X2
       grind)
    | exact superpose eq57 eq57
    | exact resolve eq57 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op y X1) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq560 eq55
    | exact resolve eq55 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq760 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq93 eq553
    | exact resolve eq553 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq553
  have eq891 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 (M.op X0 X1)
       have i₂ := eq626 X1 X0
       grind)
    | exact superpose eq626 eq9
    | exact resolve eq9 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq945 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq891 X1 (M.op X0 X0)
       have i₂ := eq891 X0 X0
       grind)
    | exact superpose eq891 eq891
    | exact resolve eq891 eq891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq954 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq1120 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq322 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq322
    | (have j0 := eq322 X0 X1
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq322 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq1760 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq945 X0 X1
       grind)
    | exact superpose eq945 eq9
    | exact resolve eq9 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1767 : y = (M.op (M.op y y) (M.op x y)) := by
    first
    | (have i₁ := eq56 (M.op y y)
       have i₂ := eq945 y x
       grind)
    | exact superpose eq945 eq56
    | exact resolve eq56 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1776 : (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq58 (M.op sF3 sF3)
       have i₂ := eq945 sF3 sF2
       grind)
    | exact superpose eq945 eq58
    | exact resolve eq58 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq1781 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq95 x (M.op sF4 sF4)
       have i₂ := eq945 sF4 (M.op (M.op sF2 x) sF3)
       grind)
    | exact superpose eq945 eq95
    | exact resolve eq95 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq945
  have eq1957 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op (M.op X0 X0) X2) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 (M.op X1 X0) (M.op X0 X0) X2
       have i₂ := eq1760 X0 X1
       grind)
    | exact superpose eq1760 eq55
    | exact resolve eq55 eq1760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2073 : ∀ X0 : G, (k (τ X0) (τ (M.op X0 X0))) = (τ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq173 X0 (M.op X0 X0)
       have i₂ := eq954 X0
       grind)
    | exact superpose eq954 eq173
    | exact resolve eq173 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq5488 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq346
       have i₂ := eq100 x
       grind)
    | exact superpose eq100 eq346
    | (have j1 := eq100 (σ x)
       grind)
    | exact resolve eq346 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq7279 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op y x) (M.op x y)) := by
    first
    | exact superpose eq695 eq55
    | exact resolve eq55 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq695
  have eq11922 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 (M.op (M.op X0 X0) X1) x X0
       have i₂ := eq1957 X0 (M.op (M.op (M.op (M.op X0 X0) X1) x) X0) X1
       grind)
    | exact superpose eq1957 eq57
    | exact resolve eq57 eq1957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq1957
  have eq12222 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11922 (M.op X1 X1) X1
       have i₂ := eq1760 X1 X1
       grind)
    | exact superpose eq1760 eq11922
    | exact resolve eq11922 eq1760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1760 eq11922
  have eq14457 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq663 (M.op X1 X0) X1 X0
       have i₂ := eq304 X1 (M.op X1 X0) X0
       grind)
    | exact superpose eq304 eq663
    | exact resolve eq663 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304 eq663
  have eq14963 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X2) (M.op (M.op (M.op X1 X0) X1) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 X0) X1) X0
       have i₂ := eq14457 X0 X1
       grind)
    | exact superpose eq14457 eq9
    | exact resolve eq9 eq14457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14457
  have eq20433 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq39 eq348
    | exact resolve eq348 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq20465 : (σ (k x x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq61 eq20433
    | exact resolve eq20433 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20433
  have eq100002 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (M.op X0 (σ y)) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1776 eq14963
    | exact resolve eq14963 eq1776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14963
  have eq120440 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1120 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1120
    | (have j0 := eq1120 x y
       grind)
    | exact resolve eq1120 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq120488 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq120440
    | exact resolve eq120440 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120440
  have eq120489 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq120488
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq120488
    | exact resolve eq120488 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120488
  have eq120490 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq120489
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq120489
    | exact resolve eq120489 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120489
  have eq120491 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq120490
    | exact resolve eq120490 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120490
  have eq120492 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq120491
       have r₂ := eq28
       grind)
    | exact resolve eq120491 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120491
  have eq120493 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq120492
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq120492
    | exact resolve eq120492 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120492
  have eq120494 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq120493
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq120493
    | exact resolve eq120493 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120493
  have eq120495 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq120494
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq120494
    | exact resolve eq120494 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120494
  have eq120496 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq120495
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq120495
    | exact resolve eq120495 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120495
  have eq120646 : (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq120496 eq12222
    | exact resolve eq12222 eq120496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120496
  have eq120666 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq120646
       have i₂ := eq891 sF2 sF2
       grind)
    | exact superpose eq891 eq120646
    | exact resolve eq120646 eq891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120646
  have eq120771 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq120666
  have eq120886 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq62 eq120771
    | exact resolve eq120771 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120771
  have eq120900 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq120886
    | exact resolve eq120886 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120886
  have eq143216 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq120900
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq120900
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq120900 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120900
  have eq143247 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq143216
  have eq143258 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq143247
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq143247
    | exact resolve eq143247 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143247
  have eq143264 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq143258
    | exact resolve eq143258 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143258
  have eq143268 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq143264
       have r₂ := eq28
       grind)
    | exact resolve eq143264 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143264
  have eq143446 : y = (M.op (M.op x x) (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12222 y y
       have i₂ := eq143268
       grind)
    | exact superpose eq143268 eq12222
    | exact resolve eq12222 eq143268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143268
  have eq143487 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq143446
       have i₂ := eq891 x x
       grind)
    | exact superpose eq891 eq143446
    | exact resolve eq143446 eq891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891 eq143446
  have eq143614 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  have eq143703 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12222 x x
       have i₂ := eq143487
       grind)
    | exact superpose eq143487 eq12222
    | exact resolve eq12222 eq143487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12222 eq143487
  have eq143748 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq143614
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq143614
    | exact resolve eq143614 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143614
  have eq144077 : (τ x) = (k (τ y) (τ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq343 y
       have i₂ := eq143703
       grind)
    | exact superpose eq143703 eq343
    | exact resolve eq343 eq143703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq143703
  have eq144180 : (τ x) = (k (τ y) (τ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq144077
  have eq151675 : (σ (τ x)) = (k y (σ (τ y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq50 y (τ y)
       have i₂ := eq144180
       grind)
    | exact superpose eq144180 eq50
    | exact resolve eq50 eq144180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq144180
  have eq151680 : (k y y) = (σ (τ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq151675
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq151675
    | exact resolve eq151675 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151675
  have eq151688 : x = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq151680
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq151680
    | exact resolve eq151680 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151680
  have eq151700 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq347
       have i₂ := eq151688
       grind)
    | exact superpose eq151688 eq347
    | exact resolve eq347 eq151688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq151720 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq151700
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq151700
    | exact resolve eq151700 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151700
  have eq170689 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq151720 eq100002
    | exact resolve eq100002 eq151720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100002
  have eq170821 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1776 eq170689
    | exact resolve eq170689 eq1776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776 eq170689
  have eq172330 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq151720 eq170821
    | exact resolve eq170821 eq151720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170821
  have eq172515 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq172330
  have eq172604 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq172515 eq954
    | exact resolve eq954 eq172515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172515
  have eq172714 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq62 eq172604
    | exact resolve eq172604 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq172604
  have eq172723 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq172714
    | exact resolve eq172714 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172714
  have eq173516 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq172723
       have i₂ := eq143748
       grind)
    | exact superpose eq143748 eq172723
    | exact resolve eq172723 eq143748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172723
  have eq173550 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq173516
  have eq173561 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq173550
    | exact resolve eq173550 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173550
  have eq173568 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq173561
       have r₂ := eq28
       grind)
    | exact resolve eq173561 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173561
  have eq173572 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq173568 eq28
    | exact resolve eq28 eq173568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173623 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq173568 eq760
    | exact resolve eq760 eq173568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760
  have eq173651 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq173568 eq1781
    | exact resolve eq1781 eq173568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1781 eq173568
  have eq173988 : (τ (σ y)) = (k (τ (M.op (σ y) (σ y))) (τ (σ y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq173623 eq200
    | exact resolve eq200 eq173623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq173623
  have eq174100 : y = (k (τ (M.op (σ y) (σ y))) y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq40 eq173988
    | exact resolve eq173988 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173988
  have eq174125 : (τ (σ y)) = (k (τ (σ y)) (τ (M.op (σ y) (σ y)))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq173651 eq2073
    | exact resolve eq2073 eq173651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2073 eq173651
  have eq174306 : y = (k y (τ (M.op (σ y) (σ y)))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq40 eq174125
    | exact resolve eq174125 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174125
  have eq181804 : y = (k (τ (σ y)) y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq151720 eq174100
    | exact resolve eq174100 eq151720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151720 eq174100
  have eq181831 : y = (k (τ (σ y)) y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq181804
  have eq181852 : y = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq40 eq181831
    | exact resolve eq181831 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181831
  have eq203629 : x = y ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq151688
       have i₂ := eq181852
       grind)
    | exact superpose eq181852 eq151688
    | exact resolve eq151688 eq181852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151688 eq181852
  have eq203645 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq203629
  have eq203688 : y = (k y (τ (σ x))) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq203645 eq174306
    | exact resolve eq174306 eq203645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174306 eq203645
  have eq203893 : y = (k y (τ (σ x))) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq203688
  have eq203911 : y = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq39 eq203893
    | exact resolve eq203893 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203893
  have eq206459 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq143748
       have i₂ := eq203911
       grind)
    | exact superpose eq203911 eq143748
    | exact resolve eq143748 eq203911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143748 eq203911
  have eq206478 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq206459
  have eq206544 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq206478 eq40
    | exact resolve eq40 eq206478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq206478
  have eq206780 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq39 eq206544
    | exact resolve eq206544 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206544
  have eq206781 : y = (M.op x y) ∨ x = y := by grind
  clear eq206780
  have eq206785 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq206781 eq21
    | exact resolve eq21 eq206781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207284 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq206785
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq206785
    | exact resolve eq206785 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206785
  have eq207563 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq207284 eq173572
    | (have r₁ := eq173572
       have r₂ := eq207284
       grind)
    | exact resolve eq173572 eq207284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173572 eq207284
  have eq207696 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq207563
  have eq207697 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq207696
  have eq207728 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq207697 eq39
    | exact resolve eq39 eq207697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq207697
  have eq207993 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq38 eq207728
    | exact resolve eq207728 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq207728
  have eq208376 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq207993 eq206781
    | exact resolve eq206781 eq207993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206781 eq207993
  have eq208377 : x = y := by grind
  clear eq208376
  have eq208429 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq208377
       grind)
    | exact superpose eq208377 eq19
    | exact resolve eq19 eq208377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq208430 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq208377
       grind)
    | exact superpose eq208377 eq25
    | exact resolve eq25 eq208377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq208561 : x = (M.op (M.op x x) (M.op x y)) := by
    first
    | (have i₁ := eq1767
       have i₂ := eq208377
       grind)
    | exact superpose eq208377 eq1767
    | exact resolve eq1767 eq208377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1767
  have eq208993 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) (M.op x y)) := by
    first
    | (have i₁ := eq7279
       have i₂ := eq208377
       grind)
    | exact superpose eq208377 eq7279
    | exact resolve eq7279 eq208377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7279 eq208377
  have eq220028 : x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq208993 eq208561
    | exact resolve eq208561 eq208993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208561 eq208993
  have eq220138 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq208430
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq208430
    | exact resolve eq208430 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208430
  have eq220146 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5488
       have i₂ := eq208429
       grind)
    | exact superpose eq208429 eq5488
    | exact resolve eq5488 eq208429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5488
  have eq220152 : x = (M.op x y) ∨ (σ (k x x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq20465
       have i₂ := eq208429
       grind)
    | exact superpose eq208429 eq20465
    | exact resolve eq20465 eq208429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20465
  have eq223490 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq220138 eq27
    | exact resolve eq27 eq220138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq220138
  have eq230958 : (σ (M.op x y)) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq220152
       have i₂ := eq208429
       grind)
    | exact superpose eq208429 eq220152
    | exact resolve eq220152 eq208429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220152
  have eq230959 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq220146
    | exact resolve eq220146 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220146
  have eq232886 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq223490 eq346
    | exact resolve eq346 eq223490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq234208 : (σ (M.op x y)) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq230958
    | exact resolve eq230958 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230958
  have eq234209 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq223490 eq230959
    | exact resolve eq230959 eq223490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230959
  have eq236454 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq223490 eq232886
    | exact resolve eq232886 eq223490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232886
  have eq236469 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq234209
       have r₂ := eq28
       grind)
    | exact resolve eq234209 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234209
  have eq237786 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq223490 eq236469
    | exact resolve eq236469 eq223490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236469
  have eq238157 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq237786
       have i₂ := eq208429
       grind)
    | exact superpose eq208429 eq237786
    | exact resolve eq237786 eq208429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237786
  have eq238369 : (k x (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq954 x
       have i₂ := eq208429
       grind)
    | exact superpose eq208429 eq954
    | exact resolve eq954 eq208429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954 eq208429
  have eq238714 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq239416 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq238157 eq238714
    | exact resolve eq238714 eq238157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238157 eq238714
  have eq239417 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq223490 eq239416
    | exact resolve eq239416 eq223490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223490 eq239416
  have eq239425 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq61 eq239417
    | exact resolve eq239417 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq239417
  have eq242488 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq234208
       have i₂ := eq239425
       grind)
    | exact superpose eq239425 eq234208
    | exact resolve eq234208 eq239425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234208 eq239425
  have eq242511 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq242488
  have eq242526 : x = (M.op x y) := by
    first
    | (have r₁ := eq242511
       have r₂ := eq28
       grind)
    | exact resolve eq242511 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242511
  have eq242537 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq242526 eq21
    | exact resolve eq21 eq242526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq245311 : x = (M.op x x) := by
    first
    | exact superpose eq242526 eq220028
    | exact resolve eq220028 eq242526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220028
  have eq245448 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq242526 eq238369
    | exact resolve eq238369 eq242526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238369 eq242526
  have eq245624 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq236454
       have i₂ := eq245448
       grind)
    | exact superpose eq245448 eq236454
    | exact resolve eq236454 eq245448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236454 eq245448
  have eq246368 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq242537
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq242537
    | exact resolve eq242537 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242537
  have eq246426 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq245624
       have i₂ := eq245311
       grind)
    | exact superpose eq245311 eq245624
    | exact resolve eq245624 eq245311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245311 eq245624
  have eq248919 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq246368 eq23
    | exact resolve eq23 eq246368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq250678 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq246368 eq246426
    | exact resolve eq246426 eq246368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246368 eq246426
  have eq253215 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq250678
       have r₂ := eq28
       grind)
    | exact resolve eq250678 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250678
  have eq255108 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq253215
       have i₂ := eq248919
       grind)
    | exact superpose eq248919 eq253215
    | exact resolve eq253215 eq248919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248919 eq253215
  have eq256192 : False := by grind
  exact eq256192

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pyx_x_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq175 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op x X0)) = X0 := by
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
  have eq176 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : y = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | (have i₁ := eq175 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq175
    | (have j0 := eq175 y
       grind)
    | exact resolve eq175 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq187 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq183 eq16
    | exact resolve eq16 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq192 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ y)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq196 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq192 eq16
    | exact resolve eq16 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq697 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
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
  have eq713 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq725 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq807 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq697
       grind)
    | exact superpose eq697 eq40
    | exact resolve eq40 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq808 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq807
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq807
    | exact resolve eq807 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq810 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq808
    | exact resolve eq808 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq820 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq810 eq713
    | exact resolve eq713 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713 eq810
  have eq827 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq820
       have r₂ := eq27
       grind)
    | exact resolve eq820 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820
  have eq839 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq827 eq182
    | exact resolve eq182 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq842 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq827 eq839
    | exact resolve eq839 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827 eq839
  have eq846 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq842 eq142
    | exact resolve eq142 eq842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq842
  have eq849 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq846
    | exact resolve eq846 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq846
  have eq852 : x = (M.op x x) := by
    first
    | (have j1 := eq725 x
       grind)
    | (have r₁ := eq849
       have r₂ := eq725 x
       grind)
    | exact resolve eq849 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq858 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq179 x
       have i₂ := eq852
       grind)
    | exact superpose eq852 eq179
    | exact resolve eq179 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq864 : (k x x) = (M.op x x) := by
    first
    | (have i₁ := eq182 x
       have i₂ := eq852
       grind)
    | exact superpose eq852 eq182
    | exact resolve eq182 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq867 : x = (k x x) := by
    first
    | (have i₁ := eq864
       have i₂ := eq852
       grind)
    | exact superpose eq852 eq864
    | exact resolve eq864 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852 eq864
  have eq868 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq858
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq858
    | exact resolve eq858 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq858
  have eq870 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq867
       grind)
    | exact superpose eq867 eq40
    | exact resolve eq40 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq867
  have eq873 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq870
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq870
    | exact resolve eq870 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq870
  have eq876 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq868 eq187
    | exact resolve eq187 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq892 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq873 eq725
    | (have j0 := eq725 (σ x)
       grind)
    | (have r₁ := eq725 (σ x)
       have r₂ := eq873
       grind)
    | exact resolve eq725 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725 eq873
  have eq893 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq892
  have eq901 : (M.op x y) = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq876
       grind)
    | exact superpose eq876 eq28
    | exact resolve eq28 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq906 : (k (M.op x y) y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq182 y
       have i₂ := eq876
       grind)
    | exact superpose eq876 eq182
    | exact resolve eq182 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876
  have eq913 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq893 eq180
    | exact resolve eq180 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq893
  have eq923 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq913
    | exact resolve eq913 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq913
  have eq925 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq923 eq196
    | exact resolve eq196 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq923
  have eq940 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq925 eq28
    | exact resolve eq28 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq945 : (M.op (σ y) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq925 eq182
    | exact resolve eq182 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq1527 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq901
       grind)
    | exact superpose eq901 eq41
    | exact resolve eq41 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq901
  have eq1529 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1527
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1527
    | exact resolve eq1527 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1527
  have eq1531 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq1529
    | exact resolve eq1529 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529
  have eq1594 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq940 eq1531
    | exact resolve eq1531 eq940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1601 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1594
       have r₂ := eq27
       grind)
    | exact resolve eq1594 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594
  have eq1620 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1601 eq945
    | exact resolve eq945 eq1601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945 eq1601
  have eq1630 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq925 eq1620
    | exact resolve eq1620 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925 eq1620
  have eq1638 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1531 eq1630
    | exact resolve eq1630 eq1531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1531 eq1630
  have eq1645 : y = (M.op x y) := by
    first
    | (have r₁ := eq1638
       have r₂ := eq27
       grind)
    | exact resolve eq1638 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1638
  have eq1653 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1645
       grind)
    | exact superpose eq1645 eq24
    | exact resolve eq24 eq1645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1670 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq906
       have i₂ := eq1645
       grind)
    | exact superpose eq1645 eq906
    | exact resolve eq906 eq1645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq1676 : y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq868 eq1670
    | exact resolve eq1670 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868 eq1670
  have eq1683 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1676
       have i₂ := eq1645
       grind)
    | exact superpose eq1645 eq1676
    | exact resolve eq1676 eq1645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645 eq1676
  have eq1694 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1653 eq20
    | exact resolve eq20 eq1653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1653
  have eq2105 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1683 eq38
    | exact resolve eq38 eq1683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq1683
  have eq2114 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq2105
    | exact resolve eq2105 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2105
  have eq2116 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq1694 eq2114
    | exact resolve eq2114 eq1694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2114
  have eq2361 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2116 eq940
    | exact resolve eq940 eq2116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940 eq2116
  have eq2370 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2361
  have eq2381 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq2370 eq27
    | exact resolve eq27 eq2370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2370
  have eq2415 : False := by grind
  exact eq2415
