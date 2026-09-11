import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxy_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq4016 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq5496 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq4016 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq4016 X0 X1
       grind)
    | exact superpose eq4016 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq4016 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq4016 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq4016 X0 X1
       grind)
    | exact resolve eq13 eq4016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4016
  have eq5527 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq5496 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5496
  have eq5528 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq5527 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5527
  have eq5534 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5528 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5528
    | (have j0 := eq5528 X0 X1
       grind)
    | exact resolve eq5528 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5528
  have eq5535 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq5534 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5534
  have eq9832 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq9836 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5535 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq5535
    | (have j0 := eq5535 (τ X1) (τ X0)
       grind)
    | exact resolve eq5535 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq9874 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9836 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9836
    | (have j0 := eq9836 X0 X1
       grind)
    | exact resolve eq9836 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9836
  have eq9891 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9874 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq9874
    | (have j0 := eq9874 X0 X1
       grind)
    | exact resolve eq9874 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9874
  have eq9896 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9891 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq9891
    | (have j0 := eq9891 X0 X1
       grind)
    | exact resolve eq9891 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9891
  have eq9901 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9896 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9896
    | (have j0 := eq9896 X0 X1
       grind)
    | exact resolve eq9896 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9896
  have eq9906 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9901 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9901
    | (have j0 := eq9901 X0 X1
       grind)
    | exact resolve eq9901 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9901
  have eq9915 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5535 X0 X1
       have i₂ := eq9906 X1 X0
       grind)
    | exact superpose eq9906 eq5535
    | (have j0 := eq5535 X0 X1
       have j1 := eq9906 (σ X1) (σ X0)
       grind)
    | exact resolve eq5535 eq9906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5535
  have eq435123 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9915 x y
       grind)
    | exact superpose eq9915 eq16
    | (have j1 := eq9915 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq9915 x y
       grind)
    | exact resolve eq16 eq9915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9915
  have eq435459 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq435123
  have eq435493 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq435459
  have eq435801 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq435493
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq435493
    | exact resolve eq435493 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435493
  have eq435811 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq9906 eq435801
    | (have j1 := eq9906 y x
       grind)
    | exact resolve eq435801 eq9906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9906 eq435801
  have eq435816 : y = (M.op x x) := by
    first
    | (have r₁ := eq435811
       have r₂ := eq16
       grind)
    | exact resolve eq435811 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435811
  have eq435817 : (M.op x y) = (k y x) := by grind
  have eq435821 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq9832 x
       have i₂ := eq435816
       grind)
    | exact superpose eq435816 eq9832
    | exact resolve eq9832 eq435816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9832 eq435816
  have eq436133 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq435821
       have r₂ := eq16
       grind)
    | exact resolve eq435821 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435821
  have eq437511 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq436133
  have eq437819 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq437511
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq437511
    | exact resolve eq437511 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437511
  have eq437829 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq437819
       have i₂ := eq435817
       grind)
    | exact superpose eq435817 eq437819
    | exact resolve eq437819 eq435817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435817 eq437819
  have eq437834 : False := by grind
  exact eq437834

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pxy_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
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
  have eq54 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq14 X0 X1 X3
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
  have eq85 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq85
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq85
    | exact resolve eq85 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq91
    | exact resolve eq91 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq92
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq92
    | exact resolve eq92 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq108 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq381 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq108 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq108
    | (have j0 := eq108 (σ X0)
       grind)
    | exact resolve eq108 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq108 x
       grind)
    | exact superpose eq108 eq44
    | (have j1 := eq108 x
       grind)
    | exact resolve eq44 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq498 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 (M.op X2 X0) X2 x X1
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq500 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq501 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq56
  have eq6215 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq381 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq69434 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq93 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69435 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq69434
    | exact resolve eq69434 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69434
  have eq69446 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq69435
       have r₂ := eq28
       grind)
    | exact resolve eq69435 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69435
  have eq69448 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq69446
    | exact resolve eq69446 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69446
  have eq69505 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq69448 eq498
    | exact resolve eq498 eq69448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69448
  have eq69577 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq501 eq69505
    | exact resolve eq69505 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69505
  have eq69613 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq69577
  have eq69741 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq69613
    | exact resolve eq69613 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69613
  have eq70034 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq69741 eq93
    | exact resolve eq93 eq69741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq69741
  have eq70042 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq70034
  have eq70044 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq70042
       have r₂ := eq28
       grind)
    | exact resolve eq70042 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70042
  have eq70349 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x (M.op x y))) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq498 x X0 x
       have i₂ := eq70044
       grind)
    | exact superpose eq70044 eq498
    | exact resolve eq498 eq70044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70044
  have eq70421 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq500 eq70349
    | exact resolve eq70349 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500 eq70349
  have eq70458 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq70421
  have eq70586 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq70458
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq70458
    | exact resolve eq70458 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70458
  have eq70635 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq70586
       grind)
    | exact superpose eq70586 eq72
    | exact resolve eq72 eq70586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq70586
  have eq70653 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq70635
    | exact resolve eq70635 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70635
  have eq70687 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq70653 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq70653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70690 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq70687
    | exact resolve eq70687 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70687
  have eq70701 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq70690
       have r₂ := eq28
       grind)
    | exact resolve eq70690 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70690
  have eq70703 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq70701
    | exact resolve eq70701 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70701
  have eq101250 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq70703 eq498
    | exact resolve eq498 eq70703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498 eq70703
  have eq101341 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq501 eq101250
    | exact resolve eq101250 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501 eq101250
  have eq101342 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq101341
  have eq102126 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq101342
  have eq102280 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq102126
    | exact resolve eq102126 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102126
  have eq102337 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq102280 eq70653
    | exact resolve eq70653 eq102280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70653 eq102280
  have eq102339 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq102337
  have eq102347 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq102339
       have r₂ := eq28
       grind)
    | exact resolve eq102339 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102339
  have eq103686 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq102347 eq30
    | exact resolve eq30 eq102347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq102347
  have eq103848 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq103686
    | exact resolve eq103686 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq103686
  have eq103849 : x = y := by grind
  clear eq103848
  have eq103850 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq103849
       grind)
    | exact superpose eq103849 eq19
    | exact resolve eq19 eq103849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq103851 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq103849
       grind)
    | exact superpose eq103849 eq25
    | exact resolve eq25 eq103849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq103849
  have eq104016 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq103851
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq103851
    | exact resolve eq103851 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103851
  have eq104017 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq104016 eq27
    | exact resolve eq27 eq104016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq104016
  have eq104188 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq385
       have i₂ := eq103850
       grind)
    | exact superpose eq103850 eq385
    | exact resolve eq385 eq103850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq104222 : (k (M.op x y) x) = (M.op x (M.op x y)) := by grind
  have eq104380 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq104188
    | exact resolve eq104188 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104188
  have eq104436 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq107269 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq104380 eq108
    | (have j0 := eq108 (σ x)
       grind)
    | exact resolve eq108 eq104380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq107270 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq104017 eq107269
    | exact resolve eq107269 eq104017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107269
  have eq107282 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq107270
       have r₂ := eq28
       grind)
    | exact resolve eq107270 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107270
  have eq107288 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq104017 eq107282
    | exact resolve eq107282 eq104017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107282
  have eq107335 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq107288 eq104436
    | exact resolve eq104436 eq107288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104436 eq107288
  have eq107341 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq104017 eq107335
    | exact resolve eq107335 eq104017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107335
  have eq108721 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq107341 eq104380
    | exact resolve eq104380 eq107341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104380 eq107341
  have eq108725 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq108721
  have eq108729 : x = (M.op x y) := by
    first
    | (have r₁ := eq108725
       have r₂ := eq28
       grind)
    | exact resolve eq108725 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108725
  have eq108737 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq108729 eq21
    | exact resolve eq21 eq108729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq108882 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq108729 eq104222
    | exact resolve eq104222 eq108729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104222
  have eq108890 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq108882
       have i₂ := eq103850
       grind)
    | exact superpose eq103850 eq108882
    | exact resolve eq108882 eq103850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103850 eq108882
  have eq108993 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq108737
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq108737
    | exact resolve eq108737 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108737
  have eq108997 : x = (k x x) := by
    first
    | exact superpose eq108729 eq108890
    | exact resolve eq108890 eq108729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108729 eq108890
  have eq109380 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6215 x
       have i₂ := eq108997
       grind)
    | exact superpose eq108997 eq6215
    | (have j0 := eq6215 x
       grind)
    | exact resolve eq6215 eq108997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6215 eq108997
  have eq109384 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq109380
  have eq109394 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq109384
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq109384
    | exact resolve eq109384 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq109384
  have eq109406 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq104017 eq109394
    | exact resolve eq109394 eq104017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104017 eq109394
  have eq109417 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq108993 eq109406
    | exact resolve eq109406 eq108993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108993 eq109406
  have eq109426 : False := by grind
  exact eq109426

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pyx_pxx_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X2 X1)) = (M.op X2 (M.op (M.op X3 X2) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X2) (M.op X2 X1)) X2 X3
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op X3 (M.op (M.op X0 (M.op X2 X3)) (M.op (M.op X2 X3) X1)))) = (M.op X3 X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq54 X4 (M.op (M.op X0 (M.op X2 X3)) (M.op (M.op X2 X3) X1)) X3 X2
       have i₂ := eq9 X1 (M.op X2 X3) X0
       grind)
    | exact superpose eq9 eq54
    | exact resolve eq54 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X0 (M.op (M.op X3 X0) X2))) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq54 x X2 X0 X3
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq54 X1 (M.op X0 X2) X0 x
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X1 X2)) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq70 X2 (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X1 X2)) X0)) X1
       have i₂ := eq70 (M.op X1 X2) X0 X3
       grind)
    | exact superpose eq70 eq70
    | exact resolve eq70 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X4 X1) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 X1) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq54 X3 (M.op X1 (M.op (M.op X2 X1) X0)) X1 X4
       have i₂ := eq70 X1 X0 X2
       grind)
    | exact superpose eq70 eq54
    | exact resolve eq54 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq93 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X3 X1) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq88 X0 X1 X2 X3 x
       have i₂ := eq9 (M.op (M.op X2 X1) X0) X1 x
       grind)
    | exact superpose eq9 eq88
    | exact resolve eq88 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq110 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X2 X1)) X0) = (M.op (M.op X2 X1) (M.op (M.op X4 (M.op X2 X1)) (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq54 X3 (M.op X1 (M.op X1 X0)) (M.op X2 X1) X4
       have i₂ := eq74 X1 X2 X0
       grind)
    | exact superpose eq74 eq54
    | exact resolve eq54 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X0)) X3)) = (M.op (M.op X1 (M.op X1 X0)) (M.op (M.op X4 (M.op X1 (M.op X1 X0))) X3)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq54 (M.op x X1) X3 (M.op X1 (M.op X1 X0)) X4
       have i₂ := eq74 X1 x X0
       grind)
    | exact superpose eq74 eq54
    | exact resolve eq54 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq74
  have eq115 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X0)) X3)) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq111 X0 X1 X3 x
       have i₂ := eq85 X3 X1 (M.op X1 X0) x
       grind)
    | exact superpose eq85 eq111
    | exact resolve eq111 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq116 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X0) = (M.op X1 (M.op X1 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq110 X0 X1 X2 X3 x
       have i₂ := eq85 (M.op X1 (M.op X1 X0)) X2 X1 x
       grind)
    | exact superpose eq85 eq110
    | exact resolve eq110 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq110
  have eq269 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq269 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq269
    | (have j0 := eq269 (σ X0)
       grind)
    | exact resolve eq269 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1185 : ∀ X0 X1 X2 : G, X1 ≠ X1 ∨ (M.op X1 X2) = (k X2 X1) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1297 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k X2 X1) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1185 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185
  have eq2247 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op X0 (M.op X2 X3))) X1) = (M.op (M.op X5 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) X1)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq93 (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) X1))) X3 X5 X2
       have i₂ := eq116 X1 (M.op X2 X3) X0 X4
       grind)
    | exact superpose eq116 eq93
    | exact resolve eq93 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq116
  have eq2256 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op X0 (M.op X2 X3))) X1) = (M.op (M.op X5 X3) (M.op X3 (M.op (M.op X2 (M.op X2 X3)) (M.op (M.op X2 X3) X1)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq2247 X0 X1 X2 X3 X4 X5
       have i₂ := eq115 X3 X2 (M.op (M.op X2 X3) X1)
       grind)
    | exact superpose eq115 eq2247
    | exact resolve eq2247 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq2247
  have eq2377 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X1) = (M.op (M.op X4 (M.op X0 (M.op X2 X3))) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2256 X0 X1 X2 X3 X4 x
       have i₂ := eq66 X2 X1 X2 X3 x
       grind)
    | exact superpose eq66 eq2256
    | exact resolve eq2256 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq2256
  have eq10697 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1297 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297
  have eq10698 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq10697 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10697
  have eq10795 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq10698 X0 X1
       grind)
    | (have i₁ := eq9 X0 X0 X2
       have i₂ := eq10698 X0 X1
       grind)
    | exact superpose eq10698 eq9
    | (have j1 := eq10698 X0 X1
       grind)
    | exact resolve eq9 eq10698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10915 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X4) = (M.op (M.op X2 (M.op X3 (M.op X1 X1))) X4) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2377 X3 X4 X0 X0 X2
       have i₂ := eq10698 X0 X1
       grind)
    | (have i₁ := eq2377 X0 X1 X1 X1 X4
       have i₂ := eq10698 X0 X1
       grind)
    | exact superpose eq10698 eq2377
    | (have j1 := eq10698 X0 X1
       grind)
    | exact resolve eq2377 eq10698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10698
  have eq10975 : ∀ X0 X1 X4 : G, (M.op X1 X4) = (M.op X0 X4) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq10915 X0 X1 x x X4
       have i₂ := eq2377 x X4 X1 X1 x
       grind)
    | exact superpose eq2377 eq10915
    | (have j0 := eq10915 X0 X1 x x X4
       grind)
    | exact resolve eq10915 eq2377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2377 eq10915
  have eq11075 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X1 X0))) = X0 ∨ (M.op X2 X1) = (k X1 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X2 X3
       have i₂ := eq10975 X1 X2 X0
       grind)
    | (have i₁ := eq9 x X0 X2
       have i₂ := eq10975 X0 X1 x
       grind)
    | exact superpose eq10975 eq9
    | (have j1 := eq10975 X1 X2 x
       grind)
    | exact resolve eq9 eq10975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10975
  have eq19307 : ∀ X0 X2 : G, X0 = X2 ∨ (M.op X2 X0) = (k X0 X2) ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq10795 X0 X2 x
       have i₂ := eq11075 X0 X0 X2 x
       grind)
    | exact superpose eq11075 eq10795
    | (have j0 := eq10795 X0 X2 X2
       have j1 := eq11075 X0 X0 X2 x
       grind)
    | exact resolve eq10795 eq11075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10795 eq11075
  have eq19343 : ∀ X0 X2 : G, (M.op X2 X0) = (k X0 X2) ∨ X0 = X2 := by
    intro X0 X2
    first
    | (have j0 := eq19307 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19307
  have eq19375 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19343 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq19343
    | (have j0 := eq19343 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq19343 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19386 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq19343 X1 (τ X0)
       grind)
    | exact superpose eq19343 eq18
    | (have j1 := eq19343 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq19343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq19343
  have eq19471 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19386 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19386
    | exact resolve eq19386 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19386
  have eq19541 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19471 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq19471
    | (have j0 := eq19471 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq19471 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19471
  have eq19707 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19375 y x
       grind)
    | exact superpose eq19375 eq16
    | (have j1 := eq19375 x y
       grind)
    | exact resolve eq16 eq19375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19375
  have eq19801 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq19707
       have i₂ := eq19541 x y
       grind)
    | exact superpose eq19541 eq19707
    | (have j1 := eq19541 (σ x) (σ y)
       grind)
    | (have r₁ := eq19707
       have r₂ := eq19541 x y
       grind)
    | (have r₁ := eq19707
       have r₂ := eq19541 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq19707
       have r₂ := eq19541 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq19707 eq19541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19541 eq19707
  have eq19802 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq19801
  have eq20063 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq19802
       grind)
    | exact superpose eq19802 eq10
    | exact resolve eq10 eq19802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19802
  have eq20101 : x = y ∨ x = y := by
    first
    | (have i₁ := eq20063
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq20063
    | exact resolve eq20063 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20063
  have eq20102 : x = y := by grind
  clear eq20101
  have eq20103 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20102
       grind)
    | exact superpose eq20102 eq16
    | exact resolve eq16 eq20102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20102
  have eq20104 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq20103
       have i₂ := eq270 x
       grind)
    | exact superpose eq270 eq20103
    | (have j1 := eq270 x
       grind)
    | exact resolve eq20103 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq22358 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq20104
       have i₂ := eq269 x
       grind)
    | exact superpose eq269 eq20104
    | (have j1 := eq269 (σ x)
       grind)
    | exact resolve eq20104 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22361 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq22358
  have eq22374 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq22361
       grind)
    | exact superpose eq22361 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq22361
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq22361
       grind)
    | exact resolve eq12 eq22361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22481 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq22374 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22374
  have eq22500 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq22481 (σ X0)
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq22481
    | exact resolve eq22481 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22481
  have eq22538 : (σ x) = (σ (k x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq22361
       have i₂ := eq22500 x
       grind)
    | exact superpose eq22500 eq22361
    | exact resolve eq22361 eq22500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22361 eq22500
  have eq22659 : (σ x) = (σ (k x x)) ∨ x = (M.op x x) := by grind
  clear eq22538
  have eq22671 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq22659
       grind)
    | exact superpose eq22659 eq10
    | exact resolve eq10 eq22659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22659
  have eq22719 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq22671
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22671
    | exact resolve eq22671 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22671
  have eq22726 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq269 x
       have i₂ := eq22719
       grind)
    | exact superpose eq22719 eq269
    | (have j0 := eq269 x
       grind)
    | exact resolve eq269 eq22719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq22719
  have eq22729 : x = (M.op x x) := by grind
  clear eq22726
  have eq22743 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq22729
       grind)
    | exact superpose eq22729 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq22729
       grind)
    | exact resolve eq12 eq22729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22842 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq22743 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22743
  have eq22901 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq20104
       have i₂ := eq22842 x
       grind)
    | exact superpose eq22842 eq20104
    | exact resolve eq20104 eq22842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20104 eq22842
  have eq22904 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq22901
  have eq22929 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq20103
       have i₂ := eq22904
       grind)
    | exact superpose eq22904 eq20103
    | exact resolve eq20103 eq22904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20103 eq22904
  have eq23060 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq22929
       have i₂ := eq22729
       grind)
    | exact superpose eq22729 eq22929
    | exact resolve eq22929 eq22729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22729 eq22929
  have eq23061 : False := by grind
  exact eq23061

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq22 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq22 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq27 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X1 X0
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
  have eq31 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X1 X0
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
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq37 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq38 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq40 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       have j1 := eq41 X0 X1
       grind)
    | (have r₁ := eq47 X0 X1
       have r₂ := eq41 X0 X1
       grind)
    | exact resolve eq47 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq47
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq55
    | (have j0 := eq55 X0 X1
       grind)
    | exact resolve eq55 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq55
  have eq110 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq114 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq110 X0 X1
       have j1 := eq58 X1 X0
       grind)
    | (have r₁ := eq110 X1 X1
       have r₂ := eq58 X1 X1
       grind)
    | (have r₁ := eq110 X1 X0
       have r₂ := eq58 X0 X1
       grind)
    | exact resolve eq110 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq110
  have eq336 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq114 (σ X1) (σ X0)
       grind)
    | exact superpose eq114 eq15
    | exact resolve eq15 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq336 X0 X1
       have i₂ := eq114 X1 X0
       grind)
    | exact superpose eq114 eq336
    | exact resolve eq336 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq336
  have eq346 : False := by grind
  exact eq346

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq74 : y ≠ (M.op x y) ∨ x = (M.op x x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq92 y x
       grind)
    | exact superpose eq92 eq71
    | (have j1 := eq92 y x
       grind)
    | exact resolve eq71 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117
    | exact resolve eq117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq118 eq92
    | (have j0 := eq92 (σ y) (σ x)
       grind)
    | exact resolve eq92 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq121
    | exact resolve eq121 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq122
       have r₂ := eq27
       grind)
    | exact resolve eq122 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq127 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq125
    | exact resolve eq125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq127 eq27
    | exact resolve eq27 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  clear eq22 eq37
  have eq435 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq127 eq75
    | (have r₁ := eq75
       have r₂ := eq127
       grind)
    | exact resolve eq75 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq127
  have eq436 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq435
  have eq1460 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq436 eq118
    | exact resolve eq118 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq1464 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1460
  have eq1469 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1464
       have r₂ := eq129
       grind)
    | exact resolve eq1464 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq1464
  have eq1481 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1469 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq1469
       grind)
    | exact resolve eq13 eq1469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1469
  have eq1488 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1481 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1481
  have eq1506 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1488 eq118
    | exact resolve eq118 eq1488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq1488
  have eq1509 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1506
  have eq1514 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1509
    | exact resolve eq1509 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1509
  have eq1516 : y = (M.op x y) := by
    first
    | (have r₁ := eq1514
       have r₂ := eq27
       grind)
    | exact resolve eq1514 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1514
  have eq1518 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1516 eq20
    | exact resolve eq20 eq1516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1523 : y ≠ y ∨ x = (M.op x x) ∨ y = (k y x) := by
    first
    | exact superpose eq1516 eq74
    | (have r₁ := eq74
       have r₂ := eq1516
       grind)
    | exact resolve eq74 eq1516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1528 : y = (k y x) ∨ x = (M.op x x) := by grind
  clear eq1523
  have eq1535 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1518
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1518
    | exact resolve eq1518 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518
  have eq1570 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1535 eq26
    | exact resolve eq26 eq1535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2342 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq1528
       grind)
    | exact superpose eq1528 eq71
    | exact resolve eq71 eq1528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq1528
  have eq2349 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1535 eq2342
    | exact resolve eq2342 eq1535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2342
  have eq2351 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2349
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2349
    | exact resolve eq2349 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2349
  have eq2352 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1535 eq2351
    | exact resolve eq2351 eq1535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535 eq2351
  have eq2359 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2352 eq92
    | (have j0 := eq92 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq92 eq2352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2352
  have eq2360 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x x) := by grind
  clear eq2359
  have eq2362 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1570 eq2360
    | exact resolve eq2360 eq1570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2360
  have eq2365 : x = (M.op x x) := by
    first
    | (have r₁ := eq2362
       have r₂ := eq27
       grind)
    | exact resolve eq2362 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2362
  have eq2373 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq2365
       grind)
    | exact superpose eq2365 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq2365
       grind)
    | exact resolve eq13 eq2365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2365
  have eq2383 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq2373 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2373
  have eq2402 : (k (σ (M.op x y)) (σ x)) = (σ (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq137
       have i₂ := eq2383 sF0
       grind)
    | exact superpose eq2383 eq137
    | exact resolve eq137 eq2383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq2383
  have eq2406 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1516 eq2402
    | exact resolve eq2402 eq1516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1516 eq2402
  have eq2409 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq2406
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2406
    | exact resolve eq2406 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2406
  have eq2412 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq2409
    | exact resolve eq2409 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2409
  have eq2427 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2412 eq92
    | (have j0 := eq92 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq92 eq2412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq2412
  have eq2428 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq2427
  have eq2430 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1570 eq2428
    | exact resolve eq2428 eq1570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1570 eq2428
  have eq2433 : False := by grind
  exact eq2433

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_x_pxy_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq17
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X2 X0)) (M.op X0 (M.op (M.op (M.op X1 X2) (M.op X2 X0)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) (M.op X2 X0)) X2
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op (M.op X2 X1) (M.op X1 X0)) = (k (M.op (M.op X2 X1) (M.op X1 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X2 X1) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op (M.op X2 X1) (M.op X1 X0)) X1
       grind)
    | (have r₁ := eq13 (M.op (M.op X2 X0) (M.op X0 X0)) X0
       have r₂ := eq9 X0 X0 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X4 X2) (M.op (M.op X3 X2) (M.op X2 X0)))) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 (M.op (M.op X3 X2) (M.op X2 X0)) X2 X4 X1
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op (M.op X5 X1) (M.op (M.op X4 X1) X2))) = (M.op (M.op X3 X1) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq62 (M.op (M.op X4 X1) X2) X1 X5 X3
       have i₂ := eq62 X2 X1 X4 X0
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X0) (M.op (M.op X5 (M.op X4 X0)) (M.op X0 X2))) = (M.op (M.op X3 (M.op X4 X0)) (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq62 (M.op X0 X2) (M.op X4 X0) X5 X3
       have i₂ := eq62 X2 X0 X1 X4
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X2) (M.op X2 (M.op (M.op X5 (M.op X1 X2)) X3))) = (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X1 X2) X3))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq62 (M.op (M.op X5 (M.op X1 X2)) X3) X2 X1 X4
       have i₂ := eq62 X3 (M.op X1 X2) X5 X0
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (M.op X2 X0) X2 x X1
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq62 X2 X0 X1 x
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X2 X0)) (M.op (M.op X2 (M.op X2 X0)) X3))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq77 X3 (M.op x X2) (M.op X2 (M.op X2 X0))
       have i₂ := eq77 X0 x X2
       grind)
    | exact superpose eq77 eq77
    | exact resolve eq77 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X1) X2) = (M.op (M.op X3 X1) (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq77 (M.op (M.op X4 X1) X2) X3 X1
       have i₂ := eq62 X2 X1 X4 X0
       grind)
    | exact superpose eq62 eq77
    | exact resolve eq77 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X2 X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq77 (M.op X3 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq77 X0 X2 X3
       grind)
    | exact superpose eq77 eq77
    | exact resolve eq77 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X0 (M.op (M.op X1 (M.op X1 X0)) X3))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 X3 (M.op X1 (M.op X1 X0)) (M.op x X1)
       have i₂ := eq77 X0 x X1
       grind)
    | exact superpose eq77 eq9
    | exact resolve eq9 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X0)) = (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X1 X2)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X2 X0)) (M.op X1 X2) X3
       have i₂ := eq77 X0 X1 X2
       grind)
    | exact superpose eq77 eq9
    | exact resolve eq9 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X2) = (M.op (M.op X4 X1) X2) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq93 x X1 X2 X4 X3
       have i₂ := eq9 X2 X1 x
       grind)
    | exact superpose eq9 eq93
    | exact resolve eq93 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq110 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X3))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq79 (M.op X1 (M.op X1 X0)) (M.op x X1) X3
       have i₂ := eq77 X0 x X1
       grind)
    | exact superpose eq77 eq79
    | exact resolve eq79 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X1) (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X3 X1)) X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq79 (M.op X3 X1) X2 X4
       have i₂ := eq105 X1 (M.op (M.op X2 (M.op X3 X1)) X4) X3 X0
       grind)
    | (have i₁ := eq79 (M.op X3 X1) X2 X4
       have i₂ := eq105 X1 (M.op (M.op X2 (M.op X3 X1)) X4) X0 X3
       grind)
    | exact superpose eq105 eq79
    | exact resolve eq79 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 (M.op X2 X1)) (M.op (M.op X0 X1) (M.op (M.op X2 X1) X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq77 X3 X4 (M.op X2 X1)
       have i₂ := eq105 X1 (M.op (M.op X2 X1) X3) X2 X0
       grind)
    | (have i₁ := eq77 X3 X4 (M.op X2 X1)
       have i₂ := eq105 X1 (M.op (M.op X2 X1) X3) X0 X2
       grind)
    | exact superpose eq105 eq77
    | exact resolve eq77 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq511 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq512 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq511 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq511
    | (have j0 := eq511 (σ X0) (σ X1)
       grind)
    | exact resolve eq511 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq511 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq511
    | (have j0 := eq511 (τ X0) (τ X1)
       grind)
    | exact resolve eq511 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq511 X0 (τ X1)
       grind)
    | exact superpose eq511 eq18
    | (have j1 := eq511 X0 (τ X1)
       grind)
    | exact resolve eq18 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq867 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq512 X0 X1
       have i₂ := eq511 X0 X1
       grind)
    | exact superpose eq511 eq512
    | (have j0 := eq512 X0 X1
       have j1 := eq511 (σ X0) (σ X1)
       grind)
    | exact resolve eq512 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq945 : ∀ X0 X1 X2 X3 : G, (k (σ (M.op X3 X1)) X2) = (σ (M.op (M.op X0 X1) (τ X2))) ∨ (τ X2) = (M.op (τ X2) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq520 (M.op X3 X1) X2
       have i₂ := eq105 X1 (τ X2) X3 X0
       grind)
    | (have i₁ := eq520 (M.op X3 X1) X2
       have i₂ := eq105 X1 (τ X2) X0 X3
       grind)
    | exact superpose eq105 eq520
    | (have j0 := eq520 (M.op X3 X1) X2
       grind)
    | exact resolve eq520 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq983 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 (M.op X1 X2)) (M.op (M.op X0 (M.op X1 X2)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq91 X2 X1 X3
       have i₂ := eq105 (M.op X1 X2) X3 X1 X0
       grind)
    | (have i₁ := eq91 X2 X1 X3
       have i₂ := eq105 (M.op X1 X2) X3 X0 X1
       grind)
    | exact superpose eq105 eq91
    | exact resolve eq91 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq1090 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X3 (M.op X4 X1)) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq95 X2 X3 X4 X1
       have i₂ := eq105 X1 X2 X4 X0
       grind)
    | (have i₁ := eq95 X2 X3 X4 X1
       have i₂ := eq105 X1 X2 X0 X4
       grind)
    | exact superpose eq105 eq95
    | exact resolve eq95 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1096 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 (M.op X1 (M.op X1 X0)))) = (M.op (M.op X2 (M.op X3 X1)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq95 (M.op X1 (M.op X1 X0)) X2 X3 X1
       have i₂ := eq77 X0 X3 X1
       grind)
    | exact superpose eq77 eq95
    | exact resolve eq95 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1187 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X1 X2)) (M.op X2 (M.op (M.op X0 (M.op X1 X2)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq99 X2 X1 X3
       have i₂ := eq105 (M.op X1 X2) X3 X1 X0
       grind)
    | (have i₁ := eq99 X2 X1 X3
       have i₂ := eq105 (M.op X1 X2) X3 X0 X1
       grind)
    | exact superpose eq105 eq99
    | exact resolve eq99 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq1332 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X3 X1)) X4)) = (M.op X1 (M.op X1 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq100 X4 X3 X1 X2
       have i₂ := eq105 X1 (M.op (M.op X2 (M.op X3 X1)) X4) X3 X0
       grind)
    | (have i₁ := eq100 X4 X3 X1 X2
       have i₂ := eq105 X1 (M.op (M.op X2 (M.op X3 X1)) X4) X0 X3
       grind)
    | exact superpose eq105 eq100
    | exact resolve eq100 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1450 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X1 X2)) (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq110 X2 X1 X3
       have i₂ := eq105 (M.op X1 X2) (M.op X2 X3) X1 X0
       grind)
    | (have i₁ := eq110 X2 X1 X3
       have i₂ := eq105 (M.op X1 X2) (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq105 eq110
    | exact resolve eq110 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq2202 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op X2 X3)) X0) = (M.op (M.op X5 (M.op X4 X3)) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq172 X4 X3 X2 (M.op (M.op X5 (M.op X4 X3)) X0) X1
       have i₂ := eq170 X2 X3 X5 X4 X0
       grind)
    | exact superpose eq170 eq172
    | exact resolve eq172 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170 eq172
  have eq2335 : ∀ X0 X1 X3 X4 X5 : G, (M.op X0 X3) = (M.op (M.op X4 (M.op X5 (M.op X1 X0))) X3) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq2202 X3 X1 (M.op x X1) (M.op X1 X0) X5 X4
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq2202
    | exact resolve eq2202 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2922 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) (M.op X2 X3)) (M.op X3 X0)) = (M.op (M.op X4 (M.op (M.op X1 X2) (M.op X2 X3))) (M.op (M.op (M.op X1 X2) (M.op X2 X3)) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 X3 X1 X2 (M.op (M.op X4 (M.op (M.op X1 X2) (M.op X2 X3))) (M.op (M.op (M.op X1 X2) (M.op X2 X3)) X0))
       have i₂ := eq9 X0 (M.op (M.op X1 X2) (M.op X2 X3)) X4
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2959 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op (M.op X1 X2) (M.op X2 X3)) X0)) = (M.op (M.op (M.op X1 X2) (M.op X2 X3)) (M.op (M.op X4 (M.op (M.op X1 X2) (M.op X2 X3))) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X3 (M.op (M.op (M.op X1 X2) (M.op X2 X3)) X0)) (M.op (M.op X1 X2) (M.op X2 X3)) X4
       have i₂ := eq61 X3 X1 X2 X0
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq2996 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op (M.op X2 X3) X0)) = (M.op X3 (M.op (M.op (M.op X1 X2) (M.op X2 X3)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2959 X0 X1 X2 X3 x
       have i₂ := eq100 X0 (M.op X1 X2) (M.op X2 X3) x
       grind)
    | exact superpose eq100 eq2959
    | exact resolve eq2959 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq2959
  have eq3014 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op (M.op X2 X3) X0)) = (M.op (M.op (M.op X1 X2) (M.op X2 X3)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2922 X0 X1 X2 X3 x
       have i₂ := eq95 X0 x (M.op X1 X2) (M.op X2 X3)
       grind)
    | exact superpose eq95 eq2922
    | exact resolve eq2922 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq2922
  have eq3049 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = (k (M.op (M.op X1 X0) (M.op X0 X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq3173 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X3 (M.op X4 X2)) X5))) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq983 X3 X4 X2 X5
       have i₂ := eq2202 (M.op (M.op X3 (M.op X4 X2)) X5) X4 X4 X2 X1 X0
       grind)
    | (have i₁ := eq983 X3 X4 X2 X5
       have i₂ := eq2202 (M.op (M.op X3 (M.op X4 X2)) X5) X0 X1 X2 X4 X4
       grind)
    | exact superpose eq2202 eq983
    | exact resolve eq983 eq2202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983
  have eq4014 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X0)) (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X0))) X4)))))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq79 (M.op X2 (M.op X3 X0)) X1 X4
       have i₂ := eq1096 (M.op (M.op X1 (M.op X2 (M.op X3 X0))) X4) X0 X2 X3
       grind)
    | exact superpose eq1096 eq79
    | exact resolve eq79 eq1096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4057 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X0)) (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 X4)))))) = X4 := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq4014 X0 x X2 X3 X4
       have i₂ := eq2335 X0 X3 X4 x X2
       grind)
    | exact superpose eq2335 eq4014
    | exact resolve eq4014 eq2335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4014
  have eq5052 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X2 (M.op (M.op X3 (M.op X4 X2)) X5))) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1187 X3 X4 X2 X5
       have i₂ := eq2202 (M.op X2 (M.op (M.op X3 (M.op X4 X2)) X5)) X4 X4 X2 X1 X0
       grind)
    | (have i₁ := eq1187 X3 X4 X2 X5
       have i₂ := eq2202 (M.op X2 (M.op (M.op X3 (M.op X4 X2)) X5)) X0 X1 X2 X4 X4
       grind)
    | exact superpose eq2202 eq1187
    | exact resolve eq1187 eq2202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq5925 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X3 (M.op X4 X2)) (M.op X2 X5))) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1450 X3 X4 X2 X5
       have i₂ := eq2202 (M.op (M.op X3 (M.op X4 X2)) (M.op X2 X5)) X4 X4 X2 X1 X0
       grind)
    | (have i₁ := eq1450 X3 X4 X2 X5
       have i₂ := eq2202 (M.op (M.op X3 (M.op X4 X2)) (M.op X2 X5)) X0 X1 X2 X4 X4
       grind)
    | exact superpose eq2202 eq1450
    | exact resolve eq1450 eq2202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1450
  have eq6891 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X0 (M.op X1 X2)) X3)) = (M.op X2 (M.op (M.op X4 X2) (M.op (M.op X5 X2) (M.op X2 (M.op (M.op (M.op X6 X0) (M.op X0 (M.op X1 X2))) X3))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq67 (M.op (M.op (M.op X6 X0) (M.op X0 (M.op X1 X2))) X3) X1 X2 X5 X4
       have i₂ := eq2996 X3 X6 X0 (M.op X1 X2)
       grind)
    | exact superpose eq2996 eq67
    | exact resolve eq67 eq2996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2996
  have eq6928 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X0 (M.op X1 X2)) X3)) = (M.op X2 (M.op (M.op X4 X2) (M.op (M.op X5 X2) (M.op X2 (M.op X2 X3))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq6891 X0 X1 X2 X3 X4 X5 x
       have i₂ := eq2335 X2 X1 X3 (M.op x X0) X0
       grind)
    | exact superpose eq2335 eq6891
    | exact resolve eq6891 eq2335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6891
  have eq7024 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X4 X2) X3)) = (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X0 (M.op X1 X2)) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6928 X0 X1 X2 X3 X4 x
       have i₂ := eq77 X3 x X2
       grind)
    | exact superpose eq77 eq6928
    | exact resolve eq6928 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6928
  have eq8773 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X4 (M.op X5 X0)) (M.op (M.op X4 (M.op X5 X0)) X3)) = (M.op (M.op (M.op X6 X4) (M.op X4 (M.op X5 X0))) (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X0) (M.op X0 X3))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq3014 X3 X6 X4 (M.op X5 X0)
       have i₂ := eq67 X3 X5 X0 X2 X1
       grind)
    | exact superpose eq67 eq3014
    | exact resolve eq3014 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3014
  have eq8935 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X0) (M.op X0 X3))))) = (M.op (M.op X4 (M.op X5 X0)) (M.op (M.op X4 (M.op X5 X0)) X3)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq8773 X0 X1 X2 X3 X4 X5 x
       have i₂ := eq2335 X0 X5 (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X0) (M.op X0 X3)))) (M.op x X4) X4
       grind)
    | exact superpose eq2335 eq8773
    | exact resolve eq8773 eq2335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8773
  have eq8997 : ∀ X0 X2 X3 X4 X5 : G, (M.op (M.op X2 X0) (M.op X0 X3)) = (M.op (M.op X4 (M.op X5 X0)) (M.op (M.op X4 (M.op X5 X0)) X3)) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq8935 X0 x X2 X3 X4 X5
       have i₂ := eq79 X0 x (M.op (M.op X2 X0) (M.op X0 X3))
       grind)
    | exact superpose eq79 eq8935
    | exact resolve eq8935 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8935
  have eq12643 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq513 X0 X0
       grind)
    | exact superpose eq513 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq513 X0 X0
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq513 X0 X0
       grind)
    | exact resolve eq12 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12683 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq513 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq12687 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq12643 X0 X1
       have j1 := eq12 X1 (τ X0)
       grind)
    | (have r₁ := eq12643 X0 X1
       have r₂ := eq12 X0 (τ X0)
       grind)
    | exact resolve eq12643 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12643
  have eq12696 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq12683 (σ X0)
       have i₂ := eq28 X0 (σ X0)
       grind)
    | exact superpose eq28 eq12683
    | (have j0 := eq12683 (σ X0)
       grind)
    | exact resolve eq12683 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12683
  have eq12697 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq12696 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12696
    | (have j0 := eq12696 X0
       grind)
    | exact resolve eq12696 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12696
  have eq12700 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12697 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12697
    | (have j0 := eq12697 X0
       grind)
    | exact resolve eq12697 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12697
  have eq12738 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12687 (σ X0) X1
       have i₂ := eq28 X0 (σ X0)
       grind)
    | exact superpose eq28 eq12687
    | (have j0 := eq12687 (σ X0) X1
       grind)
    | exact resolve eq12687 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq12687
  have eq12739 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12738 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12738
    | (have j0 := eq12738 X0 X1
       grind)
    | exact resolve eq12738 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12738
  have eq12742 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12739 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12739
    | (have j0 := eq12739 X0 X1
       grind)
    | exact resolve eq12739 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12739
  have eq26866 : ∀ X0 X1 X2 X3 X4 X6 X7 X8 : G, (M.op (M.op X7 X0) (M.op (M.op X8 X0) (M.op X0 (M.op (M.op X6 X0) (M.op X0 X3))))) = (M.op X0 (M.op (M.op X4 X0) (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X0) X3))))) := by
    intro X0 X1 X2 X3 X4 X6 X7 X8
    first
    | (have i₁ := eq68 X8 X0 (M.op (M.op X6 X0) (M.op X0 X3)) X7 x X4
       have i₂ := eq68 X6 X0 X3 x X2 X1
       grind)
    | exact superpose eq68 eq68
    | exact resolve eq68 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26874 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 X8 : G, (M.op X2 (M.op (M.op X4 X2) (M.op (M.op X0 (M.op X1 X2)) X3))) = (M.op (M.op X7 X2) (M.op (M.op X8 X2) (M.op X2 (M.op (M.op X5 (M.op X1 X2)) (M.op (M.op X6 (M.op X1 X2)) (M.op (M.op X1 X2) X3)))))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7 X8
    first
    | (have i₁ := eq68 X8 X2 (M.op (M.op X5 (M.op X1 X2)) (M.op (M.op X6 (M.op X1 X2)) (M.op (M.op X1 X2) X3))) X7 X1 X4
       have i₂ := eq67 X3 X0 (M.op X1 X2) X6 X5
       grind)
    | exact superpose eq67 eq68
    | exact resolve eq68 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27023 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op X3 X0) (M.op (M.op X4 (M.op X3 X0)) (M.op (M.op X5 (M.op X3 X0)) (M.op X0 X2)))) = (M.op (M.op X6 (M.op X3 X0)) (M.op (M.op X7 (M.op X3 X0)) (M.op X0 (M.op (M.op X1 X0) X2)))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq68 X7 (M.op X3 X0) (M.op X0 X2) X6 X5 X4
       have i₂ := eq62 X2 X0 X1 X3
       grind)
    | exact superpose eq62 eq68
    | exact resolve eq68 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq68
  have eq27480 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op X3 X0) (M.op (M.op X4 (M.op X3 X0)) (M.op (M.op X5 (M.op X3 X0)) (M.op X0 X2)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq27023 X0 X1 X2 X3 X4 X5 x x
       have i₂ := eq5925 x X3 X0 x X3 (M.op (M.op X1 X0) X2)
       grind)
    | exact superpose eq5925 eq27023
    | exact resolve eq27023 eq5925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5925 eq27023
  have eq27599 : ∀ X0 X1 X2 X3 X4 X7 X8 : G, (M.op X2 (M.op (M.op X4 X2) (M.op (M.op X0 (M.op X1 X2)) X3))) = (M.op (M.op X7 X2) (M.op (M.op X8 X2) (M.op (M.op X1 X2) X3))) := by
    intro X0 X1 X2 X3 X4 X7 X8
    first
    | (have i₁ := eq26874 X0 X1 X2 X3 X4 x x X7 X8
       have i₂ := eq3173 x X1 X2 x X1 (M.op (M.op X1 X2) X3)
       grind)
    | exact superpose eq3173 eq26874
    | exact resolve eq26874 eq3173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3173 eq26874
  have eq27605 : ∀ X0 X1 X2 X3 X6 X7 X8 : G, (M.op (M.op X1 X0) (M.op (M.op X2 X0) X3)) = (M.op (M.op X7 X0) (M.op (M.op X8 X0) (M.op X0 (M.op (M.op X6 X0) (M.op X0 X3))))) := by
    intro X0 X1 X2 X3 X6 X7 X8
    first
    | (have i₁ := eq26866 X0 X1 X2 X3 x X6 X7 X8
       have i₂ := eq9 (M.op (M.op X1 X0) (M.op (M.op X2 X0) X3)) X0 x
       grind)
    | exact superpose eq9 eq26866
    | exact resolve eq26866 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26866
  have eq27847 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X1 X0) X2) = (M.op X0 (M.op X0 (M.op (M.op X5 (M.op X3 X0)) (M.op X0 X2)))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq27480 X0 X1 X2 X3 x X5
       have i₂ := eq1332 X3 X0 x X3 (M.op (M.op X5 (M.op X3 X0)) (M.op X0 X2))
       grind)
    | exact superpose eq1332 eq27480
    | exact resolve eq27480 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27480
  have eq27954 : ∀ X1 X2 X3 X7 X8 : G, (M.op X2 (M.op X2 (M.op X2 X3))) = (M.op (M.op X7 X2) (M.op (M.op X8 X2) (M.op (M.op X1 X2) X3))) := by
    intro X1 X2 X3 X7 X8
    first
    | (have i₁ := eq27599 x X1 X2 X3 x X7 X8
       have i₂ := eq1332 x X2 x X1 X3
       grind)
    | exact superpose eq1332 eq27599
    | exact resolve eq27599 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27599
  have eq27958 : ∀ X0 X1 X2 X3 X7 X8 : G, (M.op (M.op X1 X0) (M.op (M.op X2 X0) X3)) = (M.op (M.op X7 X0) (M.op (M.op X8 X0) X3)) := by
    intro X0 X1 X2 X3 X7 X8
    first
    | (have i₁ := eq27605 X0 X1 X2 X3 x X7 X8
       have i₂ := eq9 X3 X0 x
       grind)
    | exact superpose eq9 eq27605
    | exact resolve eq27605 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27605
  have eq28848 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X1) (M.op (M.op X0 X1) X2)) = (M.op (M.op X4 (M.op X5 X1)) (M.op X1 X2)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq77 (M.op (M.op X4 (M.op X5 X1)) (M.op X1 X2)) X3 X1
       have i₂ := eq27847 X1 X0 X2 X5 X4
       grind)
    | exact superpose eq27847 eq77
    | exact resolve eq77 eq27847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27847
  have eq30435 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op (M.op X4 X1) X1)) (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1))) = (k (M.op (M.op X3 (M.op (M.op X4 X1) X1)) (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1))) (M.op (M.op X4 X1) X1)) ∨ (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1)) = (M.op (M.op X4 X1) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3049 (M.op (M.op X2 X3) X3) X1
       have i₂ := eq27958 X3 (M.op X2 X3) X2 X3 x x
       grind)
    | (have i₁ := eq3049 (M.op (M.op x X3) X3) X1
       have i₂ := eq27958 X3 X1 X2 X3 (M.op x X3) x
       grind)
    | exact superpose eq27958 eq3049
    | exact resolve eq3049 eq27958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3049 eq27958
  have eq30544 : ∀ X0 X1 X2 X4 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X1) X1))) = (k (M.op X1 (M.op X1 (M.op (M.op X2 X1) X1))) (M.op (M.op X4 X1) X1)) ∨ (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1)) = (M.op (M.op X4 X1) X1) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq30435 X0 X1 X2 x X4
       have i₂ := eq1090 X0 X1 (M.op (M.op X2 X1) X1) x (M.op X4 X1)
       grind)
    | exact superpose eq1090 eq30435
    | (have j0 := eq30435 X0 X1 X2 x X4
       grind)
    | exact resolve eq30435 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30435
  have eq30834 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1)) = (M.op (M.op X4 X1) X1) ∨ (k X1 (M.op (M.op X4 X1) X1)) = X1 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq30544 X0 X2 X1 X4
       have i₂ := eq79 X2 X1 X2
       grind)
    | exact superpose eq79 eq30544
    | (have j0 := eq30544 X0 X1 X2 X4
       grind)
    | exact resolve eq30544 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30544
  have eq32599 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op X6 (M.op X7 X2)) (M.op (M.op X0 (M.op X1 X2)) X3)) = (M.op (M.op X4 X2) (M.op (M.op X5 X2) (M.op X2 (M.op X2 (M.op X2 X3))))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq28848 X5 X2 (M.op X2 (M.op X2 (M.op X2 X3))) X4 X6 X7
       have i₂ := eq1096 X3 X2 X0 X1
       grind)
    | exact superpose eq1096 eq28848
    | exact resolve eq28848 eq1096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1096 eq28848
  have eq33087 : ∀ X0 X1 X2 X3 X4 X6 X7 : G, (M.op (M.op X4 X2) (M.op X2 X3)) = (M.op (M.op X6 (M.op X7 X2)) (M.op (M.op X0 (M.op X1 X2)) X3)) := by
    intro X0 X1 X2 X3 X4 X6 X7
    first
    | (have i₁ := eq32599 X0 X1 X2 X3 X4 x X6 X7
       have i₂ := eq77 (M.op X2 X3) x X2
       grind)
    | exact superpose eq77 eq32599
    | exact resolve eq32599 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32599
  have eq50200 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq867 x y
       grind)
    | exact superpose eq867 eq16
    | (have j1 := eq867 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq867 x y
       grind)
    | exact resolve eq16 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq50290 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq50200
  have eq50320 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op (σ x) X0))) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq77 X0 (σ y) (σ x)
       have i₂ := eq50290
       grind)
    | exact superpose eq50290 eq77
    | exact resolve eq77 eq50290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50322 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (M.op (σ y) X0))) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq79 (σ x) (σ y) X0
       have i₂ := eq50290
       grind)
    | exact superpose eq50290 eq79
    | exact resolve eq79 eq50290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51304 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (M.op X1 (σ y)) (M.op (σ y) X0)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq77 (M.op (σ x) (M.op (σ x) X0)) X1 (σ y)
       have i₂ := eq50320 X0
       grind)
    | exact superpose eq50320 eq77
    | exact resolve eq77 eq50320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50320
  have eq51501 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq50322 (σ x)
       have i₂ := eq50290
       grind)
    | exact superpose eq50290 eq50322
    | exact resolve eq50322 eq50290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50290 eq50322
  have eq51617 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by grind
  clear eq51501
  have eq59479 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X4 X0)) (M.op X0 (M.op (M.op X1 X0) X2))) = (M.op X0 (M.op X0 (M.op X0 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq69 X0 X1 X2 X3 X4 x
       have i₂ := eq1332 X4 X0 x X4 (M.op X0 X2)
       grind)
    | exact superpose eq1332 eq69
    | exact resolve eq69 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq60675 : ∀ X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X2) (M.op X2 (M.op (M.op X5 (M.op X1 X2)) X3))) = (M.op X2 (M.op X2 (M.op X2 X3))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq76 x X1 X2 X3 X4 X5
       have i₂ := eq1090 X1 X2 X3 x X1
       grind)
    | exact superpose eq1090 eq76
    | exact resolve eq76 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq140558 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op X4 X2) (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X0 (M.op X1 X2)) X3))) = (M.op (M.op X6 (M.op X7 X2)) (M.op (M.op X6 (M.op X7 X2)) (M.op (M.op X5 X2) X3))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq8997 X2 X4 (M.op (M.op X5 X2) X3) X6 X7
       have i₂ := eq7024 X0 X1 X2 X3 X5
       grind)
    | exact superpose eq7024 eq8997
    | exact resolve eq8997 eq7024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7024 eq8997
  have eq142290 : ∀ X0 X1 X2 X3 X4 X6 X7 : G, (M.op (M.op X6 (M.op X7 X2)) (M.op X2 (M.op X2 X3))) = (M.op (M.op X4 X2) (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X0 (M.op X1 X2)) X3))) := by
    intro X0 X1 X2 X3 X4 X6 X7
    first
    | (have i₁ := eq140558 X0 X1 X2 X3 X4 x X6 X7
       have i₂ := eq1090 x X2 X3 X6 X7
       grind)
    | exact superpose eq1090 eq140558
    | exact resolve eq140558 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090 eq140558
  have eq142896 : ∀ X0 X1 X2 X3 X6 X7 : G, (M.op X2 (M.op X2 (M.op (M.op X0 (M.op X1 X2)) X3))) = (M.op (M.op X6 (M.op X7 X2)) (M.op X2 (M.op X2 X3))) := by
    intro X0 X1 X2 X3 X6 X7
    first
    | (have i₁ := eq142290 X0 X1 X2 X3 x X6 X7
       have i₂ := eq1332 x X2 X0 X1 (M.op (M.op X0 (M.op X1 X2)) X3)
       grind)
    | exact superpose eq1332 eq142290
    | exact resolve eq142290 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142290
  have eq227545 : ∀ X0 X2 X3 X4 X5 X6 : G, (M.op (M.op X3 (M.op X4 X2)) (M.op (M.op X5 (M.op X6 X2)) (M.op X2 X0))) = X0 := by
    intro X0 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq33087 X5 X6 X2 (M.op X2 X0) x X3 X4
       have i₂ := eq77 X0 x X2
       grind)
    | exact superpose eq77 eq33087
    | exact resolve eq33087 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33087
  have eq440446 : ∀ X0 X1 X2 X3 : G, (k (τ (σ (M.op X3 X1))) X2) = (τ (σ (M.op (M.op X0 X1) (τ (σ X2))))) ∨ (τ (σ X2)) = (M.op (τ (σ X2)) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 (σ (M.op X3 X1)) X2
       have i₂ := eq945 X0 X1 (σ X2) X3
       grind)
    | exact superpose eq945 eq22
    | (have j1 := eq945 X0 X1 (σ X2) X3
       grind)
    | exact resolve eq22 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq945
  have eq440613 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (τ (σ X2))) = (k (τ (σ (M.op X3 X1))) X2) ∨ (τ (σ X2)) = (M.op (τ (σ X2)) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq440446 X0 X1 X2 X3
       have i₂ := eq10 (M.op (M.op X0 X1) (τ (σ X2)))
       grind)
    | exact superpose eq10 eq440446
    | (have j0 := eq440446 X0 X1 X2 X3
       grind)
    | exact resolve eq440446 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440446
  have eq440929 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (τ (σ X2))) = (k (M.op X3 X1) X2) ∨ (τ (σ X2)) = (M.op (τ (σ X2)) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq440613 X0 X1 X2 X3
       have i₂ := eq10 (M.op X3 X1)
       grind)
    | exact superpose eq10 eq440613
    | (have j0 := eq440613 X0 X1 X2 X3
       grind)
    | exact resolve eq440613 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440613
  have eq441045 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (k (M.op X3 X1) X2) ∨ (τ (σ X2)) = (M.op (τ (σ X2)) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq440929 X0 X1 X2 X3
       have i₂ := eq10 X2
       grind)
    | exact superpose eq10 eq440929
    | (have j0 := eq440929 X0 X1 X2 X3
       grind)
    | exact resolve eq440929 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440929
  have eq441126 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (k (M.op X3 X1) X2) ∨ (M.op X2 (M.op X3 X1)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq441045 X0 X1 X0 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq441045
    | (have j0 := eq441045 X0 X1 X2 X3
       grind)
    | exact resolve eq441045 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441045
  have eq442413 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op X5 (M.op X2 X1))) (k (M.op X0 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) X3)))))) = X3 ∨ (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) X3)))) = (M.op (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) X3)))) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq4057 (M.op X2 X1) X4 X5 X3
       have i₂ := eq441126 X2 X1 (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) X3)))) X0
       grind)
    | exact superpose eq441126 eq4057
    | (have j1 := eq441126 X0 X1 (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) X3)))) X0
       grind)
    | exact resolve eq4057 eq441126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4057 eq441126
  have eq443058 : ∀ X0 X1 X2 X3 : G, (M.op X1 (k (M.op X0 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) X3)))))) = X3 ∨ (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) X3)))) = (M.op (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) X3)))) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq442413 X0 X1 X2 X3 x x
       have i₂ := eq2335 X1 X2 (k (M.op X0 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) X3))))) x x
       grind)
    | exact superpose eq2335 eq442413
    | (have j0 := eq442413 X0 X1 X2 X3 x x
       grind)
    | exact resolve eq442413 eq2335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442413
  have eq443851 : ∀ X0 X1 X2 X3 : G, (M.op X1 (k (M.op X0 X1) (M.op X1 (M.op X1 (M.op X1 (M.op (M.op X2 X1) X3)))))) = X3 ∨ (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) X3)))) = (M.op (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) X3)))) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq443058 X0 X1 X2 X3
       have i₂ := eq27954 X2 X1 (M.op (M.op X2 X1) X3) X2 X2
       grind)
    | exact superpose eq27954 eq443058
    | (have j0 := eq443058 X0 X1 X2 X3
       grind)
    | exact resolve eq443058 eq27954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443058
  have eq444071 : ∀ X0 X1 X2 X3 : G, (M.op X1 (k (M.op X0 X1) (M.op X1 X3))) = X3 ∨ (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) X3)))) = (M.op (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) X3)))) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq443851 X0 X1 X2 X3
       have i₂ := eq79 X1 X2 X3
       grind)
    | exact superpose eq79 eq443851
    | (have j0 := eq443851 X0 X1 X2 X3
       grind)
    | exact resolve eq443851 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443851
  have eq444232 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op (M.op X2 X1) X3)))) = (M.op (M.op (M.op X2 X1) X3) (M.op X0 X1)) ∨ (M.op X1 (k (M.op X0 X1) (M.op X1 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq444071 X0 X1 X2 X3
       have i₂ := eq2335 (M.op (M.op X2 X1) X3) (M.op X2 X1) (M.op X0 X1) (M.op X2 X1) (M.op X2 X1)
       grind)
    | exact superpose eq2335 eq444071
    | (have j0 := eq444071 X0 X1 X2 X3
       grind)
    | exact resolve eq444071 eq2335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2335 eq444071
  have eq444315 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 (M.op X1 (M.op (M.op X2 X1) X3)))) = (M.op (M.op (M.op X2 X1) X3) (M.op X0 X1)) ∨ (M.op X1 (k (M.op X0 X1) (M.op X1 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq444232 X0 X1 X2 X3
       have i₂ := eq27954 X2 X1 (M.op (M.op X2 X1) X3) X2 X2
       grind)
    | exact superpose eq27954 eq444232
    | (have j0 := eq444232 X0 X1 X2 X3
       grind)
    | exact resolve eq444232 eq27954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27954 eq444232
  have eq444354 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op (M.op (M.op X2 X1) X3) (M.op X0 X1)) ∨ (M.op X1 (k (M.op X0 X1) (M.op X1 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq444315 X0 X1 X2 X3
       have i₂ := eq79 X1 X2 X3
       grind)
    | exact superpose eq79 eq444315
    | (have j0 := eq444315 X0 X1 X2 X3
       grind)
    | exact resolve eq444315 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444315
  have eq827588 : ∀ X0 X1 X4 X5 X6 : G, (M.op (M.op X5 (M.op X6 X1)) (M.op X1 (M.op X1 X4))) = (M.op X1 (M.op X1 (M.op (M.op (M.op X0 X1) X1) X4))) ∨ (k X1 (M.op (M.op X0 X1) X1)) = X1 := by
    intro X0 X1 X4 X5 X6
    first
    | (have i₁ := eq142896 (M.op x X1) (M.op x X1) X1 X4 X5 X6
       have i₂ := eq30834 x X1 x X0
       grind)
    | exact superpose eq30834 eq142896
    | (have j1 := eq30834 X0 X1 x X0
       grind)
    | exact resolve eq142896 eq30834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142896
  have eq827947 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X1 (M.op X1 X1))) = (M.op (M.op X3 (M.op X4 X1)) (M.op X1 (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1)))) ∨ (k X1 (M.op (M.op X5 X1) X1)) = X1 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq59479 X1 X5 X1 X3 X4
       have i₂ := eq30834 X0 X1 X2 X5
       grind)
    | exact superpose eq30834 eq59479
    | (have j1 := eq30834 X0 X1 X2 X5
       grind)
    | exact resolve eq59479 eq30834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq828249 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X1 (M.op X1 (M.op X1 X6))) = (M.op (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1)) (M.op X1 (M.op (M.op X4 (M.op X5 X1)) X6))) ∨ (k X1 (M.op (M.op X3 X1) X1)) = X1 := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq60675 X5 X1 X6 (M.op X3 X1) X4
       have i₂ := eq30834 X0 X1 X2 X3
       grind)
    | exact superpose eq30834 eq60675
    | (have j1 := eq30834 X0 X1 X2 X3
       grind)
    | exact resolve eq60675 eq30834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30834 eq60675
  have eq828968 : ∀ X1 X3 X6 : G, (k X1 (M.op (M.op X3 X1) X1)) = X1 ∨ (M.op X1 (M.op X1 (M.op X1 X6))) = X6 := by
    intro X1 X3 X6
    first
    | (have i₁ := eq828249 x X1 x X3 x x X6
       have i₂ := eq5052 (M.op x X1) (M.op x X1) X1 x x X6
       grind)
    | exact superpose eq5052 eq828249
    | (have j0 := eq828249 x X1 x X3 x x X6
       grind)
    | exact resolve eq828249 eq5052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5052 eq828249
  have eq829184 : ∀ X1 X2 X5 : G, (M.op X1 (M.op X1 (M.op X1 X1))) = (M.op X1 (M.op X1 (M.op X1 (M.op (M.op X2 X1) X1)))) ∨ (k X1 (M.op (M.op X5 X1) X1)) = X1 := by
    intro X1 X2 X5
    first
    | (have i₁ := eq827947 x X1 X2 x x X5
       have i₂ := eq59479 X1 x (M.op (M.op X2 X1) X1) x x
       grind)
    | exact superpose eq59479 eq827947
    | (have j0 := eq827947 x X1 X2 x x X5
       grind)
    | exact resolve eq827947 eq59479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59479 eq827947
  have eq829470 : ∀ X0 X1 X4 X5 X6 : G, (M.op (M.op X5 (M.op X6 X1)) (M.op X1 (M.op X1 X4))) = X4 ∨ (k X1 (M.op (M.op X0 X1) X1)) = X1 := by
    intro X0 X1 X4 X5 X6
    first
    | (have i₁ := eq827588 X0 X1 X4 X5 X6
       have i₂ := eq79 X1 (M.op X0 X1) X4
       grind)
    | exact superpose eq79 eq827588
    | (have j0 := eq827588 X0 X1 X4 X5 X6
       grind)
    | exact resolve eq827588 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827588
  have eq830513 : ∀ X1 X5 : G, (M.op X1 X1) = (M.op X1 (M.op X1 (M.op X1 X1))) ∨ (k X1 (M.op (M.op X5 X1) X1)) = X1 := by
    intro X1 X5
    first
    | (have i₁ := eq829184 X1 x X5
       have i₂ := eq79 X1 x X1
       grind)
    | exact superpose eq79 eq829184
    | (have j0 := eq829184 X1 x X5
       grind)
    | exact resolve eq829184 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829184
  have eq842977 : ∀ X1 X5 : G, (k X1 (M.op (M.op X5 X1) X1)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X1 X5
    first
    | exact superpose eq828968 eq830513
    | (have j0 := eq830513 X1 X5
       have j1 := eq828968 X1 X5 x
       grind)
    | exact resolve eq830513 eq828968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828968 eq830513
  have eq843283 : ∀ X0 X1 X2 : G, (k X0 (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X0) (M.op X0 X0))))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq842977 X0 x
       have i₂ := eq67 X0 x X0 X2 X1
       grind)
    | exact superpose eq67 eq842977
    | (have j0 := eq842977 X0 x
       grind)
    | exact resolve eq842977 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq852383 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (k X1 (M.op X0 (M.op X0 X0))) = (M.op X1 (M.op X0 (M.op X0 X0))) ∨ (k X0 (M.op (M.op X2 X0) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq829470 X2 X0 X0 X0 X0
       grind)
    | exact superpose eq829470 eq12
    | (have j0 := eq12 X1 (M.op X0 (M.op X0 X0))
       have j1 := eq829470 X2 X0 x x x
       grind)
    | exact resolve eq12 eq829470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829470
  have eq852851 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 (M.op X0 X0))) = (M.op X1 (M.op X0 (M.op X0 X0))) ∨ (k X0 (M.op (M.op X2 X0) X0)) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq842977 eq852383
    | (have j0 := eq852383 X0 X1 X2
       have j1 := eq842977 X0 X2
       grind)
    | exact resolve eq852383 eq842977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852383
  have eq854035 : ∀ X0 X1 X2 : G, (k X1 (M.op X0 (M.op X0 X0))) = (M.op X1 (M.op X0 (M.op X0 X0))) ∨ (k X0 (M.op (M.op X2 X0) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq852851 X0 X1 X2
       have j1 := eq842977 X0 X2
       grind)
    | (have r₁ := eq852851 X1 X1 X2
       have r₂ := eq842977 X1 x
       grind)
    | exact resolve eq852851 eq842977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852851
  have eq854866 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) ∨ (k X0 (M.op (M.op X2 X0) X0)) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq842977 eq854035
    | (have j0 := eq854035 X0 X1 X2
       have j1 := eq842977 X0 X2
       grind)
    | exact resolve eq854035 eq842977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854035
  have eq855327 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X2 X0) X0)) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq842977 eq854866
    | (have j0 := eq854866 X0 X1 X2
       have j1 := eq842977 X0 X2
       grind)
    | exact resolve eq854866 eq842977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842977 eq854866
  have eq956708 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op (M.op X1 X0) (M.op X0 X0)))) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (k (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq843283 X0 X1 (M.op x X0)
       have i₂ := eq444354 X0 X0 x X0
       grind)
    | exact superpose eq444354 eq843283
    | (have j0 := eq843283 X0 X1 x
       have j1 := eq444354 X0 X0 x X0
       grind)
    | exact resolve eq843283 eq444354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444354 eq843283
  have eq957811 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (k (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq956708 X0 x
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq956708
    | (have j0 := eq956708 X0 x
       grind)
    | exact resolve eq956708 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956708
  have eq958585 : ∀ X0 : G, (M.op X0 (k (M.op X0 X0) (M.op X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq957811 X0
       have j1 := eq12700 X0
       grind)
    | (have r₁ := eq957811 X0
       have r₂ := eq12700 X0
       grind)
    | exact resolve eq957811 eq12700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12700 eq957811
  have eq959657 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (M.op X0 X0) (M.op X0 X0)) X0 X1
       have i₂ := eq958585 X0
       grind)
    | exact superpose eq958585 eq9
    | (have j1 := eq958585 X0
       grind)
    | exact resolve eq9 eq958585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958585
  have eq964996 : ∀ X0 X1 X2 X3 : G, (k X0 X0) = (M.op (M.op (M.op X1 (M.op X2 X0)) (M.op X0 X0)) (M.op (M.op X3 (M.op (M.op X1 (M.op X2 X0)) (M.op X0 X0))) (M.op (M.op X1 (M.op X2 X0)) (M.op X0 X0)))) ∨ (M.op (M.op X1 (M.op X2 X0)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq959657 (M.op (M.op x (M.op x X0)) (M.op X0 X0)) X1
       have i₂ := eq227545 X0 X0 (M.op x (M.op x X0)) X0 x x
       grind)
    | exact superpose eq227545 eq959657
    | exact resolve eq959657 eq227545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227545 eq959657
  have eq966160 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X0)) (M.op X0 X0)))) ∨ (M.op (M.op X1 (M.op X2 X0)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq964996 X0 X1 X2 x
       have i₂ := eq1332 (M.op X1 (M.op X2 X0)) (M.op X0 X0) x (M.op X1 (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X0)) (M.op X0 X0))
       grind)
    | exact superpose eq1332 eq964996
    | (have j0 := eq964996 X0 X1 X2 x
       grind)
    | exact resolve eq964996 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964996
  have eq966644 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op X0 X0) (M.op X0 (M.op X0 (M.op X0 X0)))) ∨ (M.op (M.op X1 (M.op X2 X0)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq966160 X0 X1 X2
       have i₂ := eq1332 X0 X0 X1 X2 (M.op X0 X0)
       grind)
    | exact superpose eq1332 eq966160
    | (have j0 := eq966160 X0 X1 X2
       grind)
    | exact resolve eq966160 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332 eq966160
  have eq966872 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op (M.op X1 (M.op X2 X0)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq966644 X0 X1 X2
       have i₂ := eq77 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq77 eq966644
    | (have j0 := eq966644 X0 X1 X2
       grind)
    | exact resolve eq966644 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966644
  have eq966987 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq511 eq966872
    | (have j0 := eq966872 X0 X1 X2
       have j1 := eq511 X0 X0
       grind)
    | exact resolve eq966872 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966872
  have eq968159 : ∀ X0 X3 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X3 X0) = (k X3 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X3
    first
    | (have i₁ := eq855327 X0 X3 (M.op x (M.op x X0))
       have i₂ := eq966987 X0 x x
       grind)
    | exact superpose eq966987 eq855327
    | (have j0 := eq855327 X0 X3 x
       have j1 := eq966987 X0 x x
       grind)
    | exact resolve eq855327 eq966987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855327 eq966987
  have eq968809 : ∀ X0 X3 : G, (k X0 X0) = X0 ∨ (M.op X3 X0) = (k X3 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X3
    first
    | exact superpose eq511 eq968159
    | (have j0 := eq968159 X0 X3
       have j1 := eq511 X3 X0
       grind)
    | exact resolve eq968159 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511 eq968159
  have eq969594 : ∀ X0 X3 : G, (M.op X3 X0) = (k X3 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X3
    first
    | (have j0 := eq968809 X0 X3
       have j1 := eq12742 X0 X3
       grind)
    | (have r₁ := eq968809 X0 X3
       have r₂ := eq12742 X0 x
       grind)
    | exact resolve eq968809 eq12742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12742 eq968809
  have eq973159 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq969594 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969594
  have eq973160 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq973159 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973159
  have eq973690 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq973160 (σ X0)
       grind)
    | exact superpose eq973160 eq15
    | exact resolve eq15 eq973160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq973721 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq973160 (τ X0)
       grind)
    | exact superpose eq973160 eq31
    | exact resolve eq31 eq973160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq973784 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq973721 X0
       have i₂ := eq973160 X0
       grind)
    | exact superpose eq973160 eq973721
    | exact resolve eq973721 eq973160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973721
  have eq973815 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq973690 X0
       have i₂ := eq973160 X0
       grind)
    | exact superpose eq973160 eq973690
    | exact resolve eq973690 eq973160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973160 eq973690
  have eq974286 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (τ (M.op X0 X0)) (M.op (τ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ X0)
       have i₂ := eq973784 X0
       grind)
    | exact superpose eq973784 eq9
    | exact resolve eq9 eq973784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq974761 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq973815 X0
       grind)
    | exact superpose eq973815 eq9
    | exact resolve eq9 eq973815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq981125 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq974286 X0 (τ X0)
       have i₂ := eq973784 X0
       grind)
    | exact superpose eq973784 eq974286
    | exact resolve eq974286 eq973784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974286
  have eq981704 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq981125 X0
       have i₂ := eq973784 (M.op X0 X0)
       grind)
    | exact superpose eq973784 eq981125
    | exact resolve eq981125 eq973784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973784 eq981125
  have eq984756 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq974761 X0 (σ X0)
       have i₂ := eq973815 X0
       grind)
    | exact superpose eq973815 eq974761
    | exact resolve eq974761 eq973815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974761
  have eq985363 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq984756 X0
       have i₂ := eq973815 (M.op X0 X0)
       grind)
    | exact superpose eq973815 eq984756
    | exact resolve eq984756 eq973815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973815 eq984756
  have eq989304 : (τ (σ y)) = (M.op (τ (σ y)) (τ (M.op (σ x) (M.op (σ x) (σ y))))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq981704 (σ y)
       have i₂ := eq51304 (σ y) (σ y)
       grind)
    | exact superpose eq51304 eq981704
    | exact resolve eq981704 eq51304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51304 eq981704
  have eq989728 : y = (M.op y (τ (M.op (σ x) (M.op (σ x) (σ y))))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq989304
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq989304
    | exact resolve eq989304 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989304
  have eq989885 : y = (M.op y (τ (σ x))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq51617 eq989728
    | exact resolve eq989728 eq51617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51617 eq989728
  have eq989962 : y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq989885
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq989885
    | exact resolve eq989885 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989885
  have eq989963 : y = (M.op y x) := by grind
  clear eq989962
  have eq990110 : ∀ X0 : G, (M.op x (M.op y (M.op x X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq989963
       grind)
    | exact superpose eq989963 eq9
    | exact resolve eq9 eq989963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq990111 : ∀ X0 : G, x = (M.op y (M.op (M.op X0 y) y)) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq989963
       grind)
    | exact superpose eq989963 eq9
    | exact resolve eq9 eq989963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq990127 : ∀ X0 : G, x = (M.op (M.op X0 y) (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq77 x X0 y
       have i₂ := eq989963
       grind)
    | exact superpose eq989963 eq77
    | exact resolve eq77 eq989963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq990128 : ∀ X0 : G, (M.op x (M.op x (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq79 x y X0
       have i₂ := eq989963
       grind)
    | exact superpose eq989963 eq79
    | exact resolve eq79 eq989963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq990134 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 x) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq105 x X0 y X1
       have i₂ := eq989963
       grind)
    | exact superpose eq989963 eq105
    | exact resolve eq105 eq989963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq990153 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 x)) X1) = (M.op (M.op X0 y) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2202 X1 X0 y x X3 X2
       have i₂ := eq989963
       grind)
    | exact superpose eq989963 eq2202
    | exact resolve eq2202 eq989963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq990398 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op x (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq990110 (M.op y (M.op x X0))
       have i₂ := eq990110 X0
       grind)
    | exact superpose eq990110 eq990110
    | exact resolve eq990110 eq990110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990110
  have eq994557 : ∀ X0 : G, (M.op (M.op X0 y) y) = (M.op x (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq990128 (M.op (M.op X0 y) y)
       have i₂ := eq990111 X0
       grind)
    | exact superpose eq990111 eq990128
    | exact resolve eq990128 eq990111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990111 eq990128
  have eq1005305 : x = (M.op (M.op x (M.op x x)) (M.op y y)) := by
    first
    | (have i₁ := eq990127 (M.op x y)
       have i₂ := eq994557 x
       grind)
    | exact superpose eq994557 eq990127
    | exact resolve eq990127 eq994557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990127 eq994557
  have eq1012825 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op X1 x)) (M.op y y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1005305
       have i₂ := eq2202 (M.op y y) x x x X1 X0
       grind)
    | (have i₁ := eq1005305
       have i₂ := eq2202 (M.op y y) X0 X1 x x x
       grind)
    | exact superpose eq2202 eq1005305
    | exact resolve eq1005305 eq2202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2202 eq1005305
  have eq1112628 : (σ x) = (M.op (σ x) (σ (M.op y (M.op x x)))) := by
    first
    | (have i₁ := eq985363 x
       have i₂ := eq990134 (M.op x x) x
       grind)
    | exact superpose eq990134 eq985363
    | exact resolve eq985363 eq990134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990134
  have eq1112629 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (σ (M.op (M.op X0 (M.op X1 x)) (M.op y y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq985363 y
       have i₂ := eq990153 y (M.op y y) X0 X1
       grind)
    | exact superpose eq990153 eq985363
    | exact resolve eq985363 eq990153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985363 eq990153
  have eq1113091 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1112629 x x
       have i₂ := eq1012825 x x
       grind)
    | exact superpose eq1012825 eq1112629
    | exact resolve eq1112629 eq1012825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012825 eq1112629
  have eq1113092 : (σ x) = (M.op (σ x) (σ (M.op x (M.op y x)))) := by
    first
    | (have i₁ := eq1112628
       have i₂ := eq990398 x
       grind)
    | exact superpose eq990398 eq1112628
    | exact resolve eq1112628 eq990398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990398 eq1112628
  have eq1113223 : (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1113092
       have i₂ := eq989963
       grind)
    | exact superpose eq989963 eq1113092
    | exact resolve eq1113092 eq989963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989963 eq1113092
  have eq1113402 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op (σ x) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ y)
       have i₂ := eq1113091
       grind)
    | exact superpose eq1113091 eq9
    | exact resolve eq9 eq1113091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1118658 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq1113402 (σ (M.op x y))
       have i₂ := eq1113223
       grind)
    | exact superpose eq1113223 eq1113402
    | exact resolve eq1113402 eq1113223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113223 eq1113402
  have eq1119264 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1118658
       have i₂ := eq1113091
       grind)
    | exact superpose eq1113091 eq1118658
    | exact resolve eq1118658 eq1113091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113091 eq1118658
  have eq1119494 : False := by grind
  exact eq1119494

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_pxy_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  clear eq17
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X2 X0)) (M.op X0 (M.op (M.op (M.op X1 X2) (M.op X2 X0)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) (M.op X2 X0)) X2
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X4 X2) (M.op (M.op X3 X2) (M.op X2 X0)))) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 (M.op (M.op X3 X2) (M.op X2 X0)) X2 X4 X1
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op X0 (M.op (M.op X4 X0) X2)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq62 X2 X0 X4 x
       have i₂ := eq62 X2 X0 X1 x
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (M.op X2 X0) X2 x X1
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq62 X2 X0 X1 x
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 (M.op (M.op X1 X0) X0)) ∨ (M.op (M.op X0 X0) X2) = (k X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 X0)
       have i₂ := eq62 X0 X0 X1 X0
       grind)
    | exact superpose eq62 eq12
    | (have j0 := eq12 X2 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X1) X2) = (M.op (M.op X3 X1) (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq76 (M.op (M.op X4 X1) X2) X3 X1
       have i₂ := eq62 X2 X1 X4 X0
       grind)
    | exact superpose eq62 eq76
    | exact resolve eq76 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X2 X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq76 (M.op X3 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq76 X0 X2 X3
       grind)
    | exact superpose eq76 eq76
    | exact resolve eq76 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X0)) = (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X1 X2)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X2 X0)) (M.op X1 X2) X3
       have i₂ := eq76 X0 X1 X2
       grind)
    | exact superpose eq76 eq9
    | exact resolve eq9 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X2) = (M.op (M.op X4 X1) X2) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq90 x X1 X2 X4 X3
       have i₂ := eq9 X2 X1 x
       grind)
    | exact superpose eq9 eq90
    | exact resolve eq90 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq164 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X1) (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X3 X1)) X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq78 (M.op X3 X1) X2 X4
       have i₂ := eq101 X1 (M.op (M.op X2 (M.op X3 X1)) X4) X3 X0
       grind)
    | (have i₁ := eq78 (M.op X3 X1) X2 X4
       have i₂ := eq101 X1 (M.op (M.op X2 (M.op X3 X1)) X4) X0 X3
       grind)
    | exact superpose eq101 eq78
    | exact resolve eq78 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 (M.op X2 X1)) (M.op (M.op X0 X1) (M.op (M.op X2 X1) X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq76 X3 X4 (M.op X2 X1)
       have i₂ := eq101 X1 (M.op (M.op X2 X1) X3) X2 X0
       grind)
    | (have i₁ := eq76 X3 X4 (M.op X2 X1)
       have i₂ := eq101 X1 (M.op (M.op X2 X1) X3) X0 X2
       grind)
    | exact superpose eq101 eq76
    | exact resolve eq76 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq512 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq513 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq512 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq512
    | (have j0 := eq512 (σ X0) (σ X1)
       grind)
    | exact resolve eq512 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq521 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq512 X1 (τ X0)
       grind)
    | exact superpose eq512 eq18
    | (have j1 := eq512 X1 (τ X0)
       grind)
    | exact resolve eq18 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq874 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ (M.op (M.op X1 (τ X2)) (M.op (τ X2) X0))) X2) ∨ (τ X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq521 X0 (M.op (M.op X2 (τ X0)) (M.op (τ X0) X0))
       have i₂ := eq9 X0 (τ X0) X2
       grind)
    | exact superpose eq9 eq521
    | exact resolve eq521 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq1018 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X3 (M.op X4 X1)) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq92 X2 X3 X4 X1
       have i₂ := eq101 X1 X2 X4 X0
       grind)
    | (have i₁ := eq92 X2 X3 X4 X1
       have i₂ := eq101 X1 X2 X0 X4
       grind)
    | exact superpose eq101 eq92
    | exact resolve eq92 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq101
  have eq1845 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq513 X1 X0
       have i₂ := eq512 X1 X0
       grind)
    | exact superpose eq512 eq513
    | (have j0 := eq513 X1 X0
       have j1 := eq512 (σ X1) (σ X0)
       grind)
    | exact resolve eq513 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq2205 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op X2 X3)) X0) = (M.op (M.op X5 (M.op X4 X3)) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq166 X4 X3 X2 (M.op (M.op X5 (M.op X4 X3)) X0) X1
       have i₂ := eq164 X2 X3 X5 X4 X0
       grind)
    | exact superpose eq164 eq166
    | exact resolve eq166 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq166
  have eq2338 : ∀ X0 X1 X3 X4 X5 : G, (M.op X0 X3) = (M.op (M.op X4 (M.op X5 (M.op X1 X0))) X3) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq2205 X3 X1 (M.op x X1) (M.op X1 X0) X5 X4
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq2205
    | exact resolve eq2205 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2920 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X3) = (M.op (M.op (M.op X4 X0) (M.op X0 X1)) (M.op X1 (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X0 X1)) X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 X1 X4 X0 (M.op (M.op X0 X1) X3)
       have i₂ := eq62 X3 (M.op X0 X1) X2 (M.op X4 X0)
       grind)
    | exact superpose eq62 eq61
    | exact resolve eq61 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq62
  have eq3021 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X3) = (M.op (M.op (M.op X4 X0) (M.op X0 X1)) (M.op X1 (M.op X1 (M.op X1 X3)))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq2920 X0 X1 x X3 X4
       have i₂ := eq97 X3 X0 X1 x
       grind)
    | exact superpose eq97 eq2920
    | exact resolve eq2920 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq2920
  have eq11412 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (σ (M.op (M.op X1 (τ (σ X2))) (M.op (τ (σ X2)) X0)))) X2) ∨ (τ (σ X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (σ (M.op (M.op X1 (τ (σ X2))) (M.op (τ (σ X2)) X0))) X2
       have i₂ := eq874 X0 X1 (σ X2)
       grind)
    | exact superpose eq874 eq22
    | (have j1 := eq874 (k (τ (σ (M.op (M.op X1 (τ (σ X2))) (M.op (τ (σ X2)) X0)))) X2) X1 (σ X0)
       grind)
    | exact resolve eq22 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq874
  have eq11420 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (M.op (M.op X1 (τ (σ X2))) (M.op (τ (σ X2)) X0)) X2) ∨ (τ (σ X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11412 X0 X1 X2
       have i₂ := eq10 (M.op (M.op X1 (τ (σ X2))) (M.op (τ (σ X2)) X0))
       grind)
    | exact superpose eq10 eq11412
    | (have j0 := eq11412 (k (M.op (M.op X1 (τ (σ X2))) (M.op (τ (σ X2)) X0)) X2) X1 X0
       grind)
    | exact resolve eq11412 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11412
  have eq11431 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (M.op (M.op X1 X2) (M.op X2 X0)) X2) ∨ (τ (σ X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11420 X0 X1 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11420
    | (have j0 := eq11420 (k (M.op (M.op X1 X2) (M.op X2 X0)) X2) X1 X0
       grind)
    | exact resolve eq11420 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11420
  have eq11434 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 X2) (M.op X2 X0)) X2) = X0 ∨ (τ (σ X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11431 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11431
    | (have j0 := eq11431 X0 X1 X2
       grind)
    | exact resolve eq11431 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11431
  have eq11435 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 X2) (M.op X2 X0)) X2) = X0 ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11434 X0 X1 X2
       have i₂ := eq10 X2
       grind)
    | exact superpose eq10 eq11434
    | (have j0 := eq11434 X0 X1 X2
       grind)
    | exact resolve eq11434 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11434
  have eq12759 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X0) (M.op (M.op X4 X0) X2)) = (M.op (M.op (M.op X5 X3) (M.op X3 X0)) (M.op X0 (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq3021 X3 X0 (M.op (M.op X4 X0) X2) X5
       have i₂ := eq69 X0 X4 X2 X1
       grind)
    | (have i₁ := eq3021 X3 X0 (M.op (M.op X4 X0) X2) X5
       have i₂ := eq69 X0 X1 X2 X4
       grind)
    | exact superpose eq69 eq3021
    | exact resolve eq3021 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq12966 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X0) (M.op (M.op X1 X0) X2)) = (M.op (M.op X3 X0) (M.op (M.op X4 X0) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq12759 X0 X4 X2 X3 X1 x
       have i₂ := eq3021 X3 X0 (M.op (M.op X4 X0) X2) x
       grind)
    | exact superpose eq3021 eq12759
    | exact resolve eq12759 eq3021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3021 eq12759
  have eq13583 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X5 X1) X3) = (k (M.op (M.op X4 (M.op X0 X1)) (M.op (M.op X0 X1) (M.op (M.op X2 X1) X3))) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X5 X1) X3) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq11435 (M.op (M.op X5 X1) X3) X4 (M.op X0 X1)
       have i₂ := eq12966 X1 X5 X3 X0 X2
       grind)
    | (have i₁ := eq11435 (M.op (M.op X5 X1) X3) X4 (M.op X0 X1)
       have i₂ := eq12966 X1 X2 X3 X0 X5
       grind)
    | exact superpose eq12966 eq11435
    | (have j0 := eq11435 (M.op (M.op X5 X1) X3) X1 (k (M.op (M.op X4 (M.op X0 X1)) (M.op (M.op X0 X1) (M.op (M.op X2 X1) X3))) (M.op X0 X1))
       grind)
    | exact resolve eq11435 eq12966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12966
  have eq13594 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X5 X1) X3) = (k (M.op X1 (M.op X1 (M.op (M.op X2 X1) X3))) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X5 X1) X3) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq13583 X0 X1 X2 X3 x X5
       have i₂ := eq1018 X0 X1 (M.op (M.op X2 X1) X3) x X0
       grind)
    | exact superpose eq1018 eq13583
    | (have j0 := eq13583 X0 X1 X2 X3 x X5
       grind)
    | exact resolve eq13583 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018 eq13583
  have eq13766 : ∀ X0 X1 X3 X5 : G, (M.op (M.op X5 X1) X3) = (k X3 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X5 X1) X3) := by
    intro X0 X1 X3 X5
    first
    | (have i₁ := eq13594 X0 X1 x X3 X5
       have i₂ := eq78 X1 x X3
       grind)
    | exact superpose eq78 eq13594
    | (have j0 := eq13594 X0 X1 x X3 X5
       grind)
    | exact resolve eq13594 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13594
  have eq29957 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1845 x y
       grind)
    | exact superpose eq1845 eq16
    | (have j1 := eq1845 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1845 x y
       grind)
    | exact resolve eq16 eq1845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1845
  have eq30034 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq29957
  have eq30066 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op (σ y) X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq76 X0 (σ x) (σ y)
       have i₂ := eq30034
       grind)
    | exact superpose eq30034 eq76
    | exact resolve eq76 eq30034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30068 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op (σ x) X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq78 (σ y) (σ x) X0
       have i₂ := eq30034
       grind)
    | exact superpose eq30034 eq78
    | exact resolve eq78 eq30034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30759 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op X1 (σ x)) (M.op (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq76 (M.op (σ y) (M.op (σ y) X0)) X1 (σ x)
       have i₂ := eq30066 X0
       grind)
    | exact superpose eq30066 eq76
    | exact resolve eq76 eq30066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30066
  have eq30920 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30068 (σ y)
       have i₂ := eq30034
       grind)
    | exact superpose eq30034 eq30068
    | exact resolve eq30068 eq30034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30034 eq30068
  have eq31014 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq30920
  have eq61376 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op (M.op X3 X0) (M.op X0 X1)) ∨ (M.op X0 (k (M.op X0 X1) (M.op X2 X0))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X0 X3
       have i₂ := eq13766 X2 X0 (M.op X0 X1) X3
       grind)
    | exact superpose eq13766 eq9
    | (have j1 := eq13766 X2 X0 (M.op X0 X1) X3
       grind)
    | exact resolve eq9 eq13766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13766
  have eq204069 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op X4 (M.op X5 (M.op X0 X1))) X3) ∨ (M.op X1 (k (M.op X1 X2) (M.op X0 X1))) = X2 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq2338 (M.op X1 X2) (M.op x X1) X3 X4 X5
       have i₂ := eq61376 X1 X2 X0 x
       grind)
    | exact superpose eq61376 eq2338
    | (have j1 := eq61376 X1 X2 X0 X3
       grind)
    | exact resolve eq2338 eq61376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61376
  have eq204283 : ∀ X0 X1 X2 X3 : G, (M.op X1 (k (M.op X1 X2) (M.op X0 X1))) = X2 ∨ (M.op (M.op X1 X2) X3) = (M.op X1 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq204069 X0 X1 X2 X3 x x
       have i₂ := eq2338 X1 X0 X3 x x
       grind)
    | exact superpose eq2338 eq204069
    | (have j0 := eq204069 X0 X1 X2 X3 x x
       grind)
    | exact resolve eq204069 eq2338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204069
  have eq207698 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X1) (M.op X1 X0)) = (M.op X1 (k X0 (M.op X3 X1))) ∨ (M.op X0 X4) = (M.op X1 X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq204283 X0 X1 (M.op (M.op X2 X1) (M.op X1 X0)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq204283
    | exact resolve eq204283 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204283
  have eq249461 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X1) (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2)))) = (k X2 (M.op X4 X1)) ∨ (M.op X2 X5) = (M.op X1 X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq76 (k X2 (M.op X4 X1)) X3 X1
       have i₂ := eq207698 X2 X1 X0 X4 X5
       grind)
    | exact superpose eq207698 eq76
    | (have j1 := eq207698 X2 X1 X2 X3 X5
       grind)
    | exact resolve eq76 eq207698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207698
  have eq249921 : ∀ X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X1) X2) = (k X2 (M.op X4 X1)) ∨ (M.op X2 X5) = (M.op X1 X5) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq249461 x X1 X2 X3 X4 X5
       have i₂ := eq9 X2 X1 x
       grind)
    | exact superpose eq9 eq249461
    | (have j0 := eq249461 x X1 X2 X3 X4 X5
       grind)
    | exact resolve eq249461 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249461
  have eq252102 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X1 (M.op X2 (M.op X2 X0))) X3) = (k X3 X0) ∨ (M.op X3 X5) = (M.op (M.op X2 (M.op X2 X0)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq249921 (M.op X2 (M.op X2 X0)) X3 X1 (M.op x X2) X5
       have i₂ := eq76 X0 x X2
       grind)
    | exact superpose eq76 eq249921
    | (have j0 := eq249921 (M.op X2 (M.op X2 X0)) X3 X3 x X5
       grind)
    | exact resolve eq249921 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249921
  have eq253148 : ∀ X0 X2 X3 X5 : G, (M.op X3 X5) = (M.op (M.op X2 (M.op X2 X0)) X5) ∨ (M.op X0 X3) = (k X3 X0) := by
    intro X0 X2 X3 X5
    first
    | (have i₁ := eq252102 X0 x X2 X3 X5
       have i₂ := eq2338 X0 X2 X3 x X2
       grind)
    | exact superpose eq2338 eq252102
    | (have j0 := eq252102 X0 x X2 X3 X5
       grind)
    | exact resolve eq252102 eq2338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2338 eq252102
  have eq254084 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X3) (M.op (M.op X2 X3) X0))) = X0 ∨ (M.op X3 X1) = (k X1 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq253148 X3 X2 X1 (M.op (M.op X2 X3) (M.op (M.op X2 X3) X0))
       have i₂ := eq76 X0 X2 (M.op X2 X3)
       grind)
    | exact superpose eq76 eq253148
    | (have j0 := eq253148 X3 X2 X1 x
       grind)
    | exact resolve eq253148 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254956 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op X0 (M.op (M.op X1 X2) X3))) = X3 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X1 X2) X1
       have i₂ := eq253148 X2 X1 X0 (M.op (M.op X1 X2) X3)
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq253148 X0 X2 (M.op X2 X1) (M.op X1 X0)
       grind)
    | exact superpose eq253148 eq9
    | (have j1 := eq253148 X2 X2 X0 x
       grind)
    | exact resolve eq9 eq253148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253148
  have eq270247 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X1) X2) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq254084 (M.op X1 X2) X1 x X1
       have i₂ := eq66 X2 X0 X1 x x
       grind)
    | exact superpose eq66 eq254084
    | (have j0 := eq254084 X0 X1 X2 X1
       grind)
    | exact resolve eq254084 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq254084
  have eq297427 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (k X0 X2) ∨ (M.op (M.op X1 X2) X0) = X2 ∨ (M.op X2 X2) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11435 (M.op (M.op X1 X2) X0) X1 X2
       have i₂ := eq254956 X2 X1 X2 X0
       grind)
    | exact superpose eq254956 eq11435
    | (have j0 := eq11435 (M.op (M.op X1 X2) X0) X1 (k X0 X2)
       have j1 := eq254956 X2 X1 X2 x
       grind)
    | exact resolve eq11435 eq254956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11435 eq254956
  have eq298306 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = X2 ∨ (M.op X2 X0) = (k X0 X2) ∨ (M.op X2 X2) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq270247 eq297427
    | (have j0 := eq297427 X0 X1 X2
       have j1 := eq270247 X0 X2 X2
       grind)
    | exact resolve eq297427 eq270247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270247 eq297427
  have eq310932 : ∀ X0 X2 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) X2) = (k X2 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq81 X0 x X2
       have i₂ := eq298306 X0 x X0
       grind)
    | exact superpose eq298306 eq81
    | (have j0 := eq81 X0 x X2
       have j1 := eq298306 X0 x X0
       grind)
    | exact resolve eq81 eq298306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq298306
  have eq311575 : ∀ X0 X2 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) X2) = (k X2 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X2
    first
    | (have j0 := eq310932 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310932
  have eq311576 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = (k X2 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X2
    first
    | (have j0 := eq311575 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311575
  have eq311956 : ∀ X0 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X2
    first
    | exact superpose eq512 eq311576
    | (have j0 := eq311576 X0 X2
       have j1 := eq512 X2 X0
       grind)
    | exact resolve eq311576 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512 eq311576
  have eq313844 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq311956 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311956
  have eq313845 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq313844 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313844
  have eq314055 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq313845 (σ X0)
       grind)
    | exact superpose eq313845 eq15
    | exact resolve eq15 eq313845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq314076 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq313845 (τ X0)
       grind)
    | exact superpose eq313845 eq31
    | exact resolve eq31 eq313845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq314115 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq314076 X0
       have i₂ := eq313845 X0
       grind)
    | exact superpose eq313845 eq314076
    | exact resolve eq314076 eq313845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314076
  have eq314136 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq314055 X0
       have i₂ := eq313845 X0
       grind)
    | exact superpose eq313845 eq314055
    | exact resolve eq314055 eq313845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313845 eq314055
  have eq314413 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (τ (M.op X0 X0)) (M.op (τ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ X0)
       have i₂ := eq314115 X0
       grind)
    | exact superpose eq314115 eq9
    | exact resolve eq9 eq314115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq314746 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq314136 X0
       grind)
    | exact superpose eq314136 eq9
    | exact resolve eq9 eq314136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq319119 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq314413 X0 (τ X0)
       have i₂ := eq314115 X0
       grind)
    | exact superpose eq314115 eq314413
    | exact resolve eq314413 eq314115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314413
  have eq319628 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq319119 X0
       have i₂ := eq314115 (M.op X0 X0)
       grind)
    | exact superpose eq314115 eq319119
    | exact resolve eq319119 eq314115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314115 eq319119
  have eq321866 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq314746 X0 (σ X0)
       have i₂ := eq314136 X0
       grind)
    | exact superpose eq314136 eq314746
    | exact resolve eq314746 eq314136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314746
  have eq322388 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq321866 X0
       have i₂ := eq314136 (M.op X0 X0)
       grind)
    | exact superpose eq314136 eq321866
    | exact resolve eq321866 eq314136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314136 eq321866
  have eq324557 : (τ (σ x)) = (M.op (τ (σ x)) (τ (M.op (σ y) (M.op (σ y) (σ x))))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq319628 (σ x)
       have i₂ := eq30759 (σ x) (σ x)
       grind)
    | exact superpose eq30759 eq319628
    | exact resolve eq319628 eq30759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30759 eq319628
  have eq324902 : x = (M.op x (τ (M.op (σ y) (M.op (σ y) (σ x))))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq324557
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq324557
    | exact resolve eq324557 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324557
  have eq324966 : x = (M.op x (τ (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31014 eq324902
    | exact resolve eq324902 eq31014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31014 eq324902
  have eq324995 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq324966
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq324966
    | exact resolve eq324966 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324966
  have eq324996 : x = (M.op x y) := by grind
  clear eq324995
  have eq325029 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq324996
       grind)
    | exact superpose eq324996 eq16
    | exact resolve eq16 eq324996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325033 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 x) x)) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq324996
       grind)
    | exact superpose eq324996 eq9
    | exact resolve eq9 eq324996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325049 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq76 y X0 x
       have i₂ := eq324996
       grind)
    | exact superpose eq324996 eq76
    | exact resolve eq76 eq324996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq325050 : ∀ X0 : G, (M.op y (M.op y (M.op x X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq78 y x X0
       have i₂ := eq324996
       grind)
    | exact superpose eq324996 eq78
    | exact resolve eq78 eq324996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq325069 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 y)) X1) = (M.op (M.op X0 x) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2205 X1 X0 x y X3 X2
       have i₂ := eq324996
       grind)
    | exact superpose eq324996 eq2205
    | exact resolve eq2205 eq324996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324996
  have eq328352 : ∀ X0 : G, (M.op (M.op X0 x) x) = (M.op y (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq325050 (M.op (M.op X0 x) x)
       have i₂ := eq325033 X0
       grind)
    | exact superpose eq325033 eq325050
    | exact resolve eq325050 eq325033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325033 eq325050
  have eq341746 : y = (M.op (M.op y (M.op y y)) (M.op x x)) := by
    first
    | (have i₁ := eq325049 (M.op x x)
       have i₂ := eq328352 x
       grind)
    | exact superpose eq328352 eq325049
    | exact resolve eq325049 eq328352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325049 eq328352
  have eq346419 : ∀ X0 X1 : G, y = (M.op (M.op X0 (M.op X1 y)) (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq341746
       have i₂ := eq2205 (M.op x x) y y y X1 X0
       grind)
    | (have i₁ := eq341746
       have i₂ := eq2205 (M.op x x) X0 X1 y y y
       grind)
    | exact superpose eq2205 eq341746
    | exact resolve eq341746 eq2205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2205 eq341746
  have eq447278 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (σ (M.op (M.op X0 (M.op X1 y)) (M.op x x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq322388 x
       have i₂ := eq325069 x (M.op x x) X0 X1
       grind)
    | exact superpose eq325069 eq322388
    | exact resolve eq322388 eq325069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322388 eq325069
  have eq447628 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq447278 x x
       have i₂ := eq346419 x x
       grind)
    | exact superpose eq346419 eq447278
    | exact resolve eq447278 eq346419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346419 eq447278
  have eq447705 : False := by grind
  exact eq447705

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
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
  have eq53 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
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
  have eq74 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq92 y x
       grind)
    | exact superpose eq92 eq71
    | (have j1 := eq92 y x
       grind)
    | exact resolve eq71 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117
    | exact resolve eq117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq118 eq92
    | (have j0 := eq92 (σ y) (σ x)
       grind)
    | exact resolve eq92 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq121
    | exact resolve eq121 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq122
       have r₂ := eq27
       grind)
    | exact resolve eq122 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq127 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq125
    | exact resolve eq125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq27
    | exact resolve eq27 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq436 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq75
    | (have r₁ := eq75
       have r₂ := eq127
       grind)
    | exact resolve eq75 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq127
  have eq437 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq436
  have eq445 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq437 eq118
    | exact resolve eq118 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq449 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq445
  have eq454 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq449
       have r₂ := eq129
       grind)
    | exact resolve eq449 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq449
  have eq460 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq454 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq454
       grind)
    | exact resolve eq13 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq463 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq460 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq571 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq463 eq118
    | exact resolve eq118 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq463
  have eq574 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq571
  have eq579 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq574
    | exact resolve eq574 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq581 : x = (M.op x y) := by
    first
    | (have r₁ := eq579
       have r₂ := eq27
       grind)
    | exact resolve eq579 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq626 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq581 eq20
    | exact resolve eq20 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq629 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 x) x)) := by
    intro X0
    first
    | exact superpose eq581 eq53
    | exact resolve eq53 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq631 : x ≠ x ∨ x = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq581 eq74
    | (have r₁ := eq74
       have r₂ := eq581
       grind)
    | exact resolve eq74 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq581
  have eq635 : x = (k y x) ∨ x = (M.op x x) := by grind
  clear eq631
  have eq641 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq626
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq626
    | exact resolve eq626 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq642 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq641 eq26
    | exact resolve eq26 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq889 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq635
       grind)
    | exact superpose eq635 eq71
    | exact resolve eq71 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq896 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq641 eq889
    | exact resolve eq889 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889
  have eq898 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq896
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq896
    | exact resolve eq896 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq899 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq641 eq898
    | exact resolve eq898 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq930 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq899 eq92
    | (have j0 := eq92 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq92 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq931 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq930
  have eq933 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq642 eq931
    | exact resolve eq931 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931
  have eq936 : x = (M.op x x) := by
    first
    | (have r₁ := eq933
       have r₂ := eq27
       grind)
    | exact resolve eq933 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933
  have eq945 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq936
       grind)
    | exact superpose eq936 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq936
       grind)
    | exact resolve eq13 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq947 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 x) x)) := by
    intro X0
    first
    | (have i₁ := eq14 x x X0
       have i₂ := eq936
       grind)
    | exact superpose eq936 eq14
    | exact resolve eq14 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq952 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq945 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq954 : x = y := by
    first
    | (have i₁ := eq947 x
       have i₂ := eq629 x
       grind)
    | exact superpose eq629 eq947
    | exact resolve eq947 eq629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629 eq947
  have eq982 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq954
       grind)
    | exact superpose eq954 eq24
    | exact resolve eq24 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq954
  have eq1002 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq982
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq982
    | exact resolve eq982 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq982
  have eq1009 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq641 eq1002
    | exact resolve eq1002 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002
  have eq1054 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1009 eq642
    | exact resolve eq642 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq1105 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq952 y
       grind)
    | exact superpose eq952 eq71
    | exact resolve eq71 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq952
  have eq1110 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq641 eq1105
    | exact resolve eq1105 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641 eq1105
  have eq1114 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1009 eq1110
    | exact resolve eq1110 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009 eq1110
  have eq1117 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1114
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1114
    | exact resolve eq1114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1114
  have eq1120 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq1117
    | exact resolve eq1117 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1117
  have eq1125 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1120 eq92
    | (have j0 := eq92 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq92 eq1120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq1120
  have eq1126 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq1125
  have eq1128 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1054 eq1126
    | exact resolve eq1126 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054 eq1126
  have eq1131 : False := by grind
  exact eq1131
