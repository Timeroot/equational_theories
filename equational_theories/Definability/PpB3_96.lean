import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation909 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law909 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  clear eq28
  have eq990 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3381 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq990 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq990 X0 X1
       grind)
    | exact superpose eq990 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq990 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq990 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq990 X0 X1
       grind)
    | exact resolve eq13 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq3400 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3381 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3381
  have eq3401 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3400 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3400
  have eq3416 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3401 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3401
    | (have j0 := eq3401 X0 X1
       grind)
    | exact resolve eq3401 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3401
  have eq3417 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq3416 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3416
  have eq12730 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3417 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq3417
    | (have j0 := eq3417 (τ X0) (τ X1)
       grind)
    | exact resolve eq3417 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq12780 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12730 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq12730
    | (have j0 := eq12730 X0 X1
       grind)
    | exact resolve eq12730 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12730
  have eq12794 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12780 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12780
    | (have j0 := eq12780 X0 X1
       grind)
    | exact resolve eq12780 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12780
  have eq12795 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12794 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq12794
    | (have j0 := eq12794 X0 X1
       grind)
    | exact resolve eq12794 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12794
  have eq12796 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12795 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq12795
    | (have j0 := eq12795 X0 X1
       grind)
    | exact resolve eq12795 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12795
  have eq12797 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12796 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12796
    | (have j0 := eq12796 X0 X1
       grind)
    | exact resolve eq12796 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12796
  have eq12800 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3417 X0 X1
       have i₂ := eq12797 X0 X1
       grind)
    | exact superpose eq12797 eq3417
    | (have j0 := eq3417 X0 X1
       have j1 := eq12797 (σ (M.op X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq3417 eq12797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3417 eq12797
  have eq443582 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq12800 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12800
  have eq453163 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq443582 x y
       grind)
    | exact superpose eq443582 eq16
    | (have j1 := eq443582 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq443582 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq443582 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq443582 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq443582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443582
  have eq453435 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq453163
  have eq453648 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq453435
       grind)
    | exact superpose eq453435 eq10
    | exact resolve eq10 eq453435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453435
  have eq453899 : x = y ∨ x = y := by
    first
    | (have i₁ := eq453648
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq453648
    | exact resolve eq453648 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453648
  have eq453900 : x = y := by grind
  clear eq453899
  have eq453923 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq453900
       grind)
    | exact superpose eq453900 eq16
    | exact resolve eq16 eq453900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453900
  have eq453924 : False := by grind
  exact eq453924

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxy_pxx_pyx_Equation909 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq35 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1))) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq35
    | (have j0 := eq35 X0 X1
       grind)
    | exact resolve eq35 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq44 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq32
    | (have j0 := eq32 X0 X1
       grind)
    | exact resolve eq32 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq70 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq70 X0
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq70
    | exact resolve eq70 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq74 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq73
    | exact resolve eq73 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq165 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq41 X0 X1
       grind)
    | exact superpose eq41 eq44
    | (have j0 := eq44 X0 X1
       have j1 := eq41 (σ (M.op X0 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq44 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq44
  have eq1901 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq165 x y
       grind)
    | exact superpose eq165 eq16
    | (have j1 := eq165 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq165 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq165 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq165 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq1934 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1901
  have eq3692 : (σ y) = (M.op (σ x) (M.op (σ (M.op x x)) (σ (M.op x x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9 (σ y) (σ x)
       have i₂ := eq1934
       grind)
    | exact superpose eq1934 eq9
    | exact resolve eq9 eq1934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1934
  have eq3723 : (σ y) = (M.op (σ x) (σ (M.op (M.op x x) (M.op x x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3692
       have i₂ := eq22 (M.op x x)
       grind)
    | exact superpose eq22 eq3692
    | exact resolve eq3692 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3692
  have eq3730 : (σ y) = (M.op (σ x) (σ (M.op x (M.op x x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3723
       have i₂ := eq24 x x
       grind)
    | exact superpose eq24 eq3723
    | exact resolve eq3723 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3723
  have eq3734 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3730
       have i₂ := eq74 x
       grind)
    | exact superpose eq74 eq3730
    | exact resolve eq3730 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq3730
  have eq3735 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq3734
  have eq6921 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3735
       grind)
    | exact superpose eq3735 eq10
    | exact resolve eq10 eq3735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3735
  have eq6968 : x = y ∨ x = y := by
    first
    | (have i₁ := eq6921
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6921
    | exact resolve eq6921 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6921
  have eq6969 : x = y := by grind
  clear eq6968
  have eq10081 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6969
       grind)
    | exact superpose eq6969 eq16
    | exact resolve eq16 eq6969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6969
  have eq10082 : False := by grind
  exact eq10082

/-- `Equation947`: `x = y ◇ ((z ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pxy_pxy_pyx_Equation947 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law947 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law947.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq21
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
  have eq45 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq52 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq76 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq84 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq91 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq84
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq98
    | exact resolve eq98 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq101 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq76
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq76 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq101
  have eq114 : ∀ X1 : G, (k (M.op X1 X1) X1) = (M.op (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq131 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq162 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq190 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq208 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq42
    | (have j1 := eq11 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq42 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq214 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ x)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq317 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq434 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq317 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq317
    | (have j0 := eq317 X0 y
       grind)
    | exact resolve eq317 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq484 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X3 (M.op (M.op X2 X0) (M.op X1 X0)))) = (M.op X4 (M.op (M.op (M.op X2 X0) (M.op X1 X0)) (M.op X4 (M.op X0 (M.op X3 (M.op (M.op X2 X0) (M.op X1 X0))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op (M.op X2 X0) (M.op X1 X0)) X1 X2 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq497 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X2 X2 X1
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq754 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq114 (σ X0)
       have i₂ := eq78 X0 X0
       grind)
    | exact superpose eq78 eq114
    | (have j1 := eq78 X0 X0
       grind)
    | exact resolve eq114 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq755 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq78 X0 X1
       grind)
    | exact superpose eq78 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq78 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq78 X0 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq13 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq765 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq754 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq766 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq755 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq755 X0 X0
       have r₂ := eq13 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq755 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq755 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq767 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq765 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq765
    | (have j0 := eq765 X0
       grind)
    | exact resolve eq765 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq776 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq766 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq766
    | (have j0 := eq766 X0 X1
       grind)
    | exact resolve eq766 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq888 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq497 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq497
    | (have j0 := eq497 y x X0
       grind)
    | exact resolve eq497 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq910 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 x
       have i₂ := eq497 X1 x X0
       grind)
    | exact superpose eq497 eq14
    | exact resolve eq14 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq971 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq910 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq910 (M.op X0 X0) X0
       grind)
    | exact superpose eq910 eq910
    | exact resolve eq910 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq972 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq910 (M.op X1 X0) X0
       have i₂ := eq497 X0 X1 X0
       grind)
    | exact superpose eq497 eq910
    | exact resolve eq910 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq977 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1 X1 X0 X0
       have i₂ := eq910 X1 (M.op X0 X1)
       grind)
    | exact superpose eq910 eq53
    | exact resolve eq53 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq990 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op X1 (M.op X0 X0)) X1
       have i₂ := eq910 (M.op X1 (M.op X0 X0)) X0
       grind)
    | exact superpose eq910 eq14
    | exact resolve eq14 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq996 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq977 X0 X1
       have i₂ := eq497 X1 X0 X0
       grind)
    | exact superpose eq497 eq977
    | exact resolve eq977 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq1002 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq971 X0
       grind)
    | exact superpose eq971 eq13
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq971 X0
       grind)
    | exact resolve eq13 eq971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971
  have eq1018 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq1002 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002
  have eq1032 : y = (M.op (M.op x y) (M.op y (M.op y y))) := by
    first
    | exact superpose eq888 eq910
    | exact resolve eq910 eq888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq1389 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | exact superpose eq214 eq972
    | exact resolve eq972 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1418 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1389
       have i₂ := eq910 (M.op sF4 sF4) sF4
       grind)
    | exact superpose eq910 eq1389
    | exact resolve eq1389 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1389
  have eq1451 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1418 eq214
    | exact resolve eq214 eq1418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1418
  have eq2074 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq996 (M.op X1 X0) (M.op X0 (M.op X0 X0))
       have i₂ := eq972 X0 X1
       grind)
    | exact superpose eq972 eq996
    | exact resolve eq996 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2082 : (M.op (M.op y (M.op y y)) y) = (M.op (M.op x y) (M.op (M.op y (M.op y y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1032 eq996
    | exact resolve eq996 eq1032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq2094 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq910 X1 X0
       have i₂ := eq996 X1 X0
       grind)
    | (have i₁ := eq910 X1 X1
       have i₂ := eq996 X1 X1
       grind)
    | exact superpose eq996 eq910
    | exact resolve eq910 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2171 : (M.op (M.op y (M.op y y)) y) = (M.op (M.op x y) (M.op y (M.op (M.op y y) (M.op y y)))) := by
    first
    | (have i₁ := eq2082
       have i₂ := eq497 (M.op y y) y y
       grind)
    | exact superpose eq497 eq2082
    | exact resolve eq2082 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2082
  have eq2178 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2074 X0 X1
       have i₂ := eq497 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq497 eq2074
    | exact resolve eq2074 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2074
  have eq2213 : (M.op (M.op x y) y) = (M.op (M.op y (M.op y y)) y) := by
    first
    | (have i₁ := eq2171
       have i₂ := eq14 y y y
       grind)
    | exact superpose eq14 eq2171
    | exact resolve eq2171 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2171
  have eq2218 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2178 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq2178
    | exact resolve eq2178 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2178
  have eq2240 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq2213
       have i₂ := eq990 y y
       grind)
    | exact superpose eq990 eq2213
    | exact resolve eq2213 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2213
  have eq2245 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2218 X0 X1
       have i₂ := eq990 X0 X0
       grind)
    | exact superpose eq990 eq2218
    | exact resolve eq2218 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990 eq2218
  have eq5786 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq162 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq162
    | (have j0 := eq162 x
       grind)
    | exact resolve eq162 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq5804 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5786
  have eq5808 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5804
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq5804
    | exact resolve eq5804 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq5804
  have eq5816 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq5808
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq5808 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5808
  have eq5822 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5816 eq50
    | exact resolve eq50 eq5816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq5992 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq190 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq190
    | (have j0 := eq190 y
       grind)
    | exact resolve eq190 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq6009 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5992
  have eq6012 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6009
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq6009
    | exact resolve eq6009 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq6009
  have eq6025 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq6012
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq6012 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6012
  have eq6044 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq6025 eq106
    | exact resolve eq106 eq6025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq6071 : (k (k y y) y) = (τ (k (M.op (σ y) (σ y)) (σ y))) := by
    first
    | exact superpose eq6044 eq434
    | exact resolve eq434 eq6044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq6074 : (k (k y y) y) = (τ (M.op (M.op (σ y) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq6071
       have i₂ := eq114 sF3
       grind)
    | exact superpose eq114 eq6071
    | exact resolve eq6071 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6071
  have eq6080 : (τ (M.op (σ y) (σ y))) = (k (k y y) y) := by
    first
    | (have i₁ := eq6074
       have i₂ := eq2245 sF3 sF3
       grind)
    | exact superpose eq2245 eq6074
    | exact resolve eq6074 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6074
  have eq6082 : (k y y) = (k (k y y) y) := by
    first
    | exact superpose eq6044 eq6080
    | exact resolve eq6080 eq6044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6080
  have eq6200 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq208
    | (have j0 := eq208 (M.op x y)
       grind)
    | exact resolve eq208 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq6216 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq6200
  have eq6218 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq133 eq6216
    | exact resolve eq6216 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq6216
  have eq6236 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq6218
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6218 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6218
  have eq6620 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (σ (k (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq767 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq767
    | exact resolve eq767 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq6717 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (k X0 (σ (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6620 X0
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq6620
    | (have j0 := eq6620 X0
       grind)
    | exact resolve eq6620 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6620
  have eq6744 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6717 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6717
    | (have j0 := eq6717 X0
       grind)
    | exact resolve eq6717 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6717
  have eq6766 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6744 X0
       have i₂ := eq39 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq39 eq6744
    | (have j0 := eq6744 X0
       grind)
    | exact resolve eq6744 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq6744
  have eq6784 : ∀ X0 : G, (k (k X0 (σ (τ X0))) X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6766 X0
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq6766
    | (have j0 := eq6766 X0
       grind)
    | exact resolve eq6766 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq6766
  have eq6802 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6784 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6784
    | (have j0 := eq6784 X0
       grind)
    | exact resolve eq6784 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6784
  have eq14218 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X3 (M.op X1 (M.op X0 X0)))) = (M.op X4 (M.op (M.op X1 (M.op X0 X0)) (M.op X4 (M.op X0 (M.op X3 (M.op X1 (M.op X0 X0))))))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq484 X0 x X1 X3 X4
       have i₂ := eq497 X0 X1 x
       grind)
    | exact superpose eq497 eq484
    | exact resolve eq484 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq14292 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) (M.op X1 X1)))) = (M.op X2 (M.op (M.op (M.op X0 X1) (M.op X1 X1)) (M.op (M.op X0 X1) (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14218 X1 (M.op X0 X1) X2 X2
       have i₂ := eq53 X1 X2 X1 X0
       grind)
    | exact superpose eq53 eq14218
    | exact resolve eq14218 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq14218
  have eq14343 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) (M.op X1 X1)))) = (M.op X2 (M.op (M.op X0 X1) (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14292 X0 X1 X2
       have i₂ := eq497 (M.op X1 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq497 eq14292
    | exact resolve eq14292 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497 eq14292
  have eq14380 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) (M.op X1 X1)))) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 (M.op (M.op X1 X1) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14343 X0 X1 X2
       have i₂ := eq996 (M.op X1 X1) X1
       grind)
    | exact superpose eq996 eq14343
    | exact resolve eq14343 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14343
  have eq14408 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) (M.op X1 X1)))) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14380 X0 X1 X2
       have i₂ := eq2245 X1 X1
       grind)
    | exact superpose eq2245 eq14380
    | exact resolve eq14380 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14380
  have eq14431 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X1 (M.op X2 (M.op (M.op X0 X1) (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14408 X0 X1 X2
       have i₂ := eq972 X1 X0
       grind)
    | exact superpose eq972 eq14408
    | exact resolve eq14408 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972 eq14408
  have eq14452 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X1 (M.op X2 (M.op X1 (M.op (M.op X0 X1) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14431 X0 X1 X2
       have i₂ := eq996 (M.op X0 X1) X1
       grind)
    | exact superpose eq996 eq14431
    | exact resolve eq14431 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996 eq14431
  have eq14466 : ∀ X1 X2 : G, (M.op X2 X1) = (M.op X1 (M.op X2 (M.op X1 (M.op X1 X1)))) := by
    intro X1 X2
    first
    | (have i₁ := eq14452 x X1 X2
       have i₂ := eq2245 X1 x
       grind)
    | exact superpose eq2245 eq14452
    | exact resolve eq14452 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14452
  have eq19214 : (σ (M.op x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq5816 eq91
    | exact resolve eq91 eq5816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq5816
  have eq20374 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq100 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20381 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq20374
    | exact resolve eq20374 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20374
  have eq20392 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq20381
       have r₂ := eq28
       grind)
    | exact resolve eq20381 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20381
  have eq20394 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq20392
    | exact resolve eq20392 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20392
  have eq20396 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20394 eq5822
    | exact resolve eq5822 eq20394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5822
  have eq20402 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20394 eq114
    | exact resolve eq114 eq20394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20394
  have eq20441 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq20402
       have r₂ := eq67
       grind)
    | exact resolve eq20402 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq20402
  have eq20447 : y = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq20396
    | exact resolve eq20396 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq20396
  have eq20455 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20441 eq100
    | exact resolve eq100 eq20441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq20441
  have eq20469 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq20455
  have eq25984 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq20447
       grind)
    | exact superpose eq20447 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq20447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26000 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq25984
  have eq28893 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6025 eq107
    | exact resolve eq107 eq6025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq6025
  have eq29618 : (M.op x y) = (k x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1018 x
       have i₂ := eq26000
       grind)
    | exact superpose eq26000 eq1018
    | exact resolve eq1018 eq26000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29651 : x ≠ y ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  have eq29659 : (M.op x y) = (k x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29618
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29618
    | exact resolve eq29618 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29618
  have eq30491 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq29659
       grind)
    | exact superpose eq29659 eq45
    | exact resolve eq45 eq29659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29659
  have eq30521 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq30491
    | exact resolve eq30491 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30491
  have eq40273 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19214
       have i₂ := eq26000
       grind)
    | exact superpose eq26000 eq19214
    | exact resolve eq19214 eq26000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19214 eq26000
  have eq40358 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq40273
       have r₂ := eq29651
       grind)
    | exact resolve eq40273 eq29651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29651 eq40273
  have eq40376 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40358
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq40358
    | exact resolve eq40358 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40358
  have eq40399 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq40376 eq1018
    | exact resolve eq1018 eq40376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40376
  have eq40450 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq40399
    | exact resolve eq40399 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40399
  have eq40905 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq40450 eq30521
    | exact resolve eq30521 eq40450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30521 eq40450
  have eq40915 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq40905
  have eq40921 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq40915
       have r₂ := eq28
       grind)
    | exact resolve eq40915 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40915
  have eq41085 : (k x x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq114 x
       have i₂ := eq40921
       grind)
    | exact superpose eq40921 eq114
    | exact resolve eq114 eq40921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41086 : ∀ X0 : G, x = (M.op X0 (M.op X0 x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq910 X0 x
       have i₂ := eq40921
       grind)
    | exact superpose eq40921 eq910
    | exact resolve eq910 eq40921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910 eq40921
  have eq41947 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20447
       have i₂ := eq41085
       grind)
    | exact superpose eq41085 eq20447
    | exact resolve eq20447 eq41085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20447 eq41085
  have eq41968 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq41947
  have eq45071 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq41086 x
       have i₂ := eq41968
       grind)
    | exact superpose eq41968 eq41086
    | exact resolve eq41086 eq41968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41086 eq41968
  have eq45170 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq45071
  have eq45216 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45170
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq45170
    | exact resolve eq45170 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45170
  have eq45217 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq45216
  have eq45260 : (σ y) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45217 eq214
    | exact resolve eq214 eq45217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq45266 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45217 eq1451
    | exact resolve eq1451 eq45217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1451 eq45217
  have eq45518 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (σ x) (M.op X0 (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq45260 eq14466
    | exact resolve eq14466 eq45260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14466 eq45260
  have eq45631 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45266 eq2094
    | exact resolve eq2094 eq45266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2094 eq45266
  have eq45677 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45631 eq6044
    | exact resolve eq6044 eq45631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6044 eq45631
  have eq45765 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq45677
    | exact resolve eq45677 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq45677
  have eq45812 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6082
       have i₂ := eq45765
       grind)
    | exact superpose eq45765 eq6082
    | exact resolve eq6082 eq45765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6082
  have eq58698 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6802 y
       have i₂ := eq45765
       grind)
    | exact superpose eq45765 eq6802
    | (have j0 := eq6802 y
       grind)
    | exact resolve eq6802 eq45765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6802 eq45765
  have eq58785 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq58698
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq58698
    | exact resolve eq58698 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58698
  have eq197383 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45812
       have i₂ := eq58785
       grind)
    | exact superpose eq58785 eq45812
    | exact resolve eq45812 eq58785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58785
  have eq197412 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq197383
  have eq197566 : y ≠ y ∨ y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq197412
       grind)
    | exact superpose eq197412 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq197412
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq197412
       grind)
    | exact resolve eq13 eq197412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197412
  have eq197588 : y = (k y y) ∨ x = (M.op x y) := by grind
  clear eq197566
  have eq198485 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq776 y y
       have i₂ := eq197588
       grind)
    | exact superpose eq197588 eq776
    | (have j0 := eq776 y y
       grind)
    | exact resolve eq776 eq197588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776 eq197588
  have eq198488 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq198485
  have eq198489 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq198488
  have eq198525 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq198489
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq198489
    | exact resolve eq198489 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198489
  have eq201985 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq198525 eq45518
    | exact resolve eq45518 eq198525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45518 eq198525
  have eq202071 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq201985
  have eq202132 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq202071
    | exact resolve eq202071 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202071
  have eq207640 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq202132 eq20469
    | exact resolve eq20469 eq202132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20469 eq202132
  have eq207796 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq207640
  have eq207834 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq207796
       have r₂ := eq28
       grind)
    | exact resolve eq207796 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207796
  have eq217207 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1018 x
       have i₂ := eq207834
       grind)
    | exact superpose eq207834 eq1018
    | exact resolve eq1018 eq207834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018 eq207834
  have eq217285 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq217207
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq217207
    | exact resolve eq217207 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217207
  have eq230436 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45812
       have i₂ := eq217285
       grind)
    | exact superpose eq217285 eq45812
    | exact resolve eq45812 eq217285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45812 eq217285
  have eq230470 : x = (M.op x y) := by grind
  clear eq230436
  have eq230783 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq230470 eq21
    | exact resolve eq21 eq230470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq230885 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq230470 eq2240
    | exact resolve eq2240 eq230470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2240
  have eq231018 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq230885
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq230885
    | exact resolve eq230885 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230885
  have eq231098 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq230783
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq230783
    | exact resolve eq230783 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230783
  have eq231104 : x = (M.op y y) := by
    first
    | exact superpose eq230470 eq231018
    | exact resolve eq231018 eq230470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231018
  have eq231136 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq231098 eq27
    | exact resolve eq27 eq231098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq231762 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq28893
       have i₂ := eq231104
       grind)
    | exact superpose eq231104 eq28893
    | exact resolve eq28893 eq231104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28893
  have eq231797 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq114 y
       have i₂ := eq231104
       grind)
    | exact superpose eq231104 eq114
    | exact resolve eq114 eq231104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq231104
  have eq231881 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq231797
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq231797
    | exact resolve eq231797 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq231797
  have eq231896 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq231762
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq231762
    | exact resolve eq231762 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231762
  have eq231906 : x = (k x y) := by
    first
    | exact superpose eq230470 eq231881
    | exact resolve eq231881 eq230470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230470 eq231881
  have eq231912 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq231098 eq231896
    | exact resolve eq231896 eq231098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231896
  have eq232048 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq231906
       grind)
    | exact superpose eq231906 eq45
    | exact resolve eq45 eq231906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq231906
  have eq232131 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq231098 eq232048
    | exact resolve eq232048 eq231098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232048
  have eq232155 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq232131
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq232131
    | exact resolve eq232131 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232131
  have eq232178 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq231098 eq232155
    | exact resolve eq232155 eq231098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232155
  have eq259251 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq231912 eq2245
    | exact resolve eq2245 eq231912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2245 eq231912
  have eq259260 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq231136 eq259251
    | exact resolve eq259251 eq231136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259251
  have eq259285 : x = y := by
    first
    | (have r₁ := eq259260
       have r₂ := eq28
       grind)
    | exact resolve eq259260 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259260
  have eq259311 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq259285
       grind)
    | exact superpose eq259285 eq25
    | exact resolve eq25 eq259285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq259334 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq132
       have i₂ := eq259285
       grind)
    | exact superpose eq259285 eq132
    | exact resolve eq132 eq259285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq259285
  have eq259845 : (σ (M.op x y)) = (σ (k (M.op x y) x)) := by
    first
    | exact superpose eq232178 eq259334
    | exact resolve eq259334 eq232178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232178 eq259334
  have eq259868 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq259311
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq259311
    | exact resolve eq259311 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq259311
  have eq259999 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq131 eq259845
    | exact resolve eq259845 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq259845
  have eq260021 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq231098 eq259868
    | exact resolve eq259868 eq231098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259868
  have eq260094 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq231098 eq259999
    | exact resolve eq259999 eq231098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231098 eq259999
  have eq260154 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq6236 eq260094
    | exact resolve eq260094 eq6236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6236 eq260094
  have eq260722 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq260021 eq231136
    | exact resolve eq231136 eq260021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231136 eq260021
  have eq261603 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq260154 eq260722
    | exact resolve eq260722 eq260154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260154 eq260722
  have eq261604 : False := by grind
  exact eq261604

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pyx_y_pyx_x_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq56 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq56
    | exact resolve eq56 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq57
    | exact resolve eq57 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq57
  have eq91 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X2) (M.op X1 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X3 (M.op (M.op X2 X3) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) X3 X2
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq9
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq125 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq125 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq125
    | (have j0 := eq125 (σ X0) (σ X1)
       grind)
    | exact resolve eq125 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X1 X3 : G, (M.op X3 X3) = (M.op (M.op X1 (M.op X3 X3)) X3) := by
    intro X1 X3
    first
    | (have i₁ := eq91 x X3 (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq91
    | exact resolve eq91 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq173 : ∀ X1 X3 X4 : G, (M.op (M.op X1 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X1 X3 X4
    first
    | (have i₁ := eq29 X3 x (M.op (M.op x x) (M.op X1 X1)) X4
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq29
    | exact resolve eq29 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq206 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq140 X1 (M.op x (M.op x x))
       have i₂ := eq173 x x x
       grind)
    | exact superpose eq173 eq140
    | exact resolve eq140 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq240 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq134 y x
       grind)
    | exact superpose eq134 eq16
    | (have j1 := eq134 y x
       grind)
    | exact resolve eq16 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq713 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq99 X0 (M.op X0 X0) X2 X1
       have i₂ := eq206 X0 X0
       grind)
    | exact superpose eq206 eq99
    | exact resolve eq99 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq715 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq99 X0 X0 x (M.op X0 X0)
       have i₂ := eq173 x X0 X0
       grind)
    | exact superpose eq173 eq99
    | exact resolve eq99 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq746 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq715 (σ X0)
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq715
    | exact resolve eq715 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq852 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X1 (M.op X1 X1)))) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq99 (M.op X0 X1) X1 X3 X2
       have i₂ := eq713 X1 X1 X0
       grind)
    | exact superpose eq713 eq99
    | exact resolve eq99 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq864 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq852 X0 X1 x x
       have i₂ := eq99 X1 X1 x x
       grind)
    | exact superpose eq99 eq852
    | exact resolve eq852 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq852
  have eq1556 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq240
       have i₂ := eq125 y x
       grind)
    | exact superpose eq125 eq240
    | (have j1 := eq125 (σ y) (σ x)
       grind)
    | exact resolve eq240 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq240
  have eq1557 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1556
  have eq1571 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq864 (σ x) (σ y)
       have i₂ := eq1557
       grind)
    | exact superpose eq1557 eq864
    | exact resolve eq864 eq1557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1575 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1571
       have i₂ := eq60 y
       grind)
    | exact superpose eq60 eq1571
    | exact resolve eq1571 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq1571
  have eq11188 : (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1557
       have i₂ := eq1575
       grind)
    | exact superpose eq1575 eq1557
    | exact resolve eq1557 eq1575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1557 eq1575
  have eq11240 : (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) := by grind
  clear eq11188
  have eq11283 : (M.op y y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq11240
       grind)
    | exact superpose eq11240 eq10
    | exact resolve eq10 eq11240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11240
  have eq11323 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11283
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11283
    | exact resolve eq11283 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11283
  have eq11437 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq864 y y
       have i₂ := eq11323
       grind)
    | exact superpose eq11323 eq864
    | exact resolve eq864 eq11323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11323
  have eq11456 : x = (M.op x y) := by grind
  clear eq11437
  have eq11493 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq864 x y
       have i₂ := eq11456
       grind)
    | exact superpose eq11456 eq864
    | exact resolve eq864 eq11456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864
  have eq11522 : x = (M.op y y) := by
    first
    | (have i₁ := eq11493
       have i₂ := eq11456
       grind)
    | exact superpose eq11456 eq11493
    | exact resolve eq11493 eq11456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11493
  have eq11578 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq746 y
       have i₂ := eq11522
       grind)
    | exact superpose eq11522 eq746
    | exact resolve eq746 eq11522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746 eq11522
  have eq11956 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11578
       grind)
    | exact superpose eq11578 eq16
    | exact resolve eq16 eq11578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11578
  have eq12010 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq11956
       have i₂ := eq11456
       grind)
    | exact superpose eq11456 eq11956
    | exact resolve eq11956 eq11456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11456 eq11956
  have eq12011 : False := by grind
  exact eq12011

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_x_pxy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq85 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq86 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq85
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq85
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq96
    | exact resolve eq96 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq97
    | exact resolve eq97 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq99 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq86
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq86 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq16
    | exact resolve eq16 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq99
  have eq114 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq152 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq114
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq114
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq114 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq114 eq16
    | exact resolve eq16 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq160 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq152
  have eq165 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq104
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq104 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq167 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq165
  have eq207 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq47 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq207 eq47
    | exact resolve eq47 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : (M.op x y) = (k (M.op x y) (M.op y (M.op x y))) := by grind
  have eq368 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq50 X0 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq48 (M.op X1 X0)
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq48
    | exact resolve eq48 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X3
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq393 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq49 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq50 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq49 X0 x x X3
       grind)
    | exact superpose eq49 eq50
    | exact resolve eq50 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq626 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (σ (k X0 X0))) (M.op (σ X0) (M.op X3 X3))) = X3 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq49 (σ X0) X1 X2 X3
       have i₂ := eq63 X0 X0
       grind)
    | exact superpose eq63 eq49
    | (have j1 := eq63 X0 X0
       grind)
    | exact resolve eq49 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq639 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (σ (k X0 X0))) (M.op (σ X0) (M.op X3 X3))) = X3 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq626 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq1628 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq393 X0 X0 X0
       grind)
    | exact superpose eq393 eq14
    | exact resolve eq14 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1630 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (M.op X0 (M.op X0 X0))
       have i₂ := eq393 X0 X0 X0
       grind)
    | exact superpose eq393 eq47
    | exact resolve eq47 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1631 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (M.op X0 (M.op X0 X0))
       have i₂ := eq393 X0 X0 X0
       grind)
    | exact superpose eq393 eq48
    | exact resolve eq48 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq1874 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq368 X0
       have i₂ := eq1630 X0
       grind)
    | exact superpose eq1630 eq368
    | exact resolve eq368 eq1630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq1904 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1630 eq369
    | exact resolve eq369 eq1630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1630
  have eq1917 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq369 eq1904
    | exact resolve eq1904 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1904
  have eq1952 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq47 eq1874
    | exact resolve eq1874 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq1954 : (M.op y (M.op x y)) = (M.op (M.op y (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq210 eq1874
    | exact resolve eq1874 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq1874
  have eq2111 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1631 eq369
    | exact resolve eq369 eq1631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1631
  have eq2124 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq369 eq2111
    | exact resolve eq2111 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq2111
  have eq11114 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (σ (k y y))) (M.op (σ y) (M.op X2 X2))) = X2 ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq639 y X0 X1 X2
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq639
    | (have j0 := eq639 y X0 X1 X2
       grind)
    | exact resolve eq639 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq11190 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (k (σ y) (σ y))) (M.op (σ y) (M.op X2 X2))) = X2 ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11114 X0 X1 X2
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq11114
    | exact resolve eq11114 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11114
  have eq17465 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17466 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17465
    | exact resolve eq17465 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17465
  have eq17477 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq17466
       have r₂ := eq28
       grind)
    | exact resolve eq17466 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17466
  have eq17479 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17477
    | exact resolve eq17477 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17477
  have eq17511 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17479 eq1952
    | exact resolve eq1952 eq17479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17479
  have eq17552 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17511
    | exact resolve eq17511 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17511
  have eq17553 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17552
  have eq17587 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1952 y
       have i₂ := eq17553
       grind)
    | exact superpose eq17553 eq1952
    | exact resolve eq1952 eq17553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17553
  have eq17633 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17587
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17587
    | exact resolve eq17587 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17587
  have eq17634 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17633
  have eq17639 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17634 eq28
    | exact resolve eq28 eq17634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17640 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op X0 X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17634 eq48
    | exact resolve eq48 eq17634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq17669 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17634 eq2124
    | exact resolve eq2124 eq17634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2124
  have eq17673 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq17669
    | exact resolve eq17669 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17669
  have eq17794 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  have eq17879 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17634 eq17794
    | exact resolve eq17794 eq17634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17794
  have eq17885 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq17879
  have eq18012 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17885 eq98
    | exact resolve eq98 eq17885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq17885
  have eq18023 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq18012
  have eq19305 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1952 y
       have i₂ := eq18023
       grind)
    | exact superpose eq18023 eq1952
    | exact resolve eq1952 eq18023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1952 eq18023
  have eq19351 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq19305
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19305
    | exact resolve eq19305 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19305
  have eq19352 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq19351
  have eq19359 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19352 eq30
    | exact resolve eq30 eq19352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq19526 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq19359
    | exact resolve eq19359 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq19359
  have eq19617 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq19851 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq207 eq160
    | exact resolve eq160 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq19852 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq207 eq19851
    | exact resolve eq19851 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq19851
  have eq25268 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17673 eq17640
    | exact resolve eq17640 eq17673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17640 eq17673
  have eq25310 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by grind
  clear eq25268
  have eq25342 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17634 eq25310
    | exact resolve eq25310 eq17634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17634 eq25310
  have eq25378 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq25342
  have eq25397 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 X1) (M.op (σ y) (σ y))) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq25378 eq49
    | exact resolve eq49 eq25378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq25378
  have eq25444 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25397 x x
       have i₂ := eq427 sF3 (M.op x x)
       grind)
    | exact superpose eq427 eq25397
    | exact resolve eq25397 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427 eq25397
  have eq30196 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq412 X0 (M.op X1 X0) X2 X3 X4
       have i₂ := eq1628 X0 X0 X1
       grind)
    | exact superpose eq1628 eq412
    | exact resolve eq412 eq1628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1628
  have eq30273 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30196 X0 X1 x x x
       have i₂ := eq412 X0 X0 x x x
       grind)
    | exact superpose eq412 eq30196
    | exact resolve eq30196 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412 eq30196
  have eq35211 : (M.op y (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq19852 eq16
    | exact resolve eq16 eq19852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19852
  have eq35267 : (k (M.op x y) (M.op x y)) = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq155 eq35211
    | exact resolve eq35211 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35211
  have eq264763 : (M.op (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq11190 eq371
    | exact resolve eq371 eq11190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371 eq11190
  have eq3388428 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25444 eq167
    | exact resolve eq167 eq25444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167 eq25444
  have eq3389036 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq3388428
    | exact resolve eq3388428 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3388428
  have eq3389054 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq3389036
       grind)
    | exact superpose eq3389036 eq86
    | exact resolve eq86 eq3389036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq3389036
  have eq3389532 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3389054
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3389054
    | exact resolve eq3389054 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3389054
  have eq3390032 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19352 eq3389532
    | exact resolve eq3389532 eq19352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19352 eq3389532
  have eq3390309 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq3390032
  have eq3390376 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3390309
       have r₂ := eq17639
       grind)
    | exact resolve eq3390309 eq17639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17639 eq3390309
  have eq3390417 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3390376 eq155
    | exact resolve eq155 eq3390376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq3390376
  have eq3390727 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq3390417
    | exact resolve eq3390417 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3390417
  have eq3391390 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq35267 eq3390727
    | exact resolve eq3390727 eq35267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35267
  have eq3553887 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq3391390 eq212
    | exact resolve eq212 eq3391390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq3391390
  have eq3609970 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq3553887 eq3390727
    | exact resolve eq3390727 eq3553887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3390727 eq3553887
  have eq3610261 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq3609970
  have eq3613716 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3610261 eq1954
    | exact resolve eq1954 eq3610261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1954 eq3610261
  have eq3614781 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq19526 eq3613716
    | exact resolve eq3613716 eq19526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19526 eq3613716
  have eq3615498 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3614781
       have r₂ := eq19617
       grind)
    | exact resolve eq3614781 eq19617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19617 eq3614781
  have eq3615593 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3615498
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3615498
    | exact resolve eq3615498 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3615498
  have eq3615594 : x = (M.op x y) := by grind
  clear eq3615593
  have eq3626784 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq3615594 eq21
    | exact resolve eq21 eq3615594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq3626900 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq3615594 eq1917
    | exact resolve eq1917 eq3615594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1917
  have eq3627467 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq3626900
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3626900
    | exact resolve eq3626900 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3626900
  have eq3627538 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3626784
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3626784
    | exact resolve eq3626784 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3626784
  have eq3627616 : x = (M.op y y) := by
    first
    | exact superpose eq3615594 eq3627467
    | exact resolve eq3627467 eq3615594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3615594 eq3627467
  have eq3627648 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq3627538 eq27
    | exact resolve eq27 eq3627538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq3629532 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq105
       have i₂ := eq3627616
       grind)
    | exact superpose eq3627616 eq105
    | exact resolve eq105 eq3627616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq3629604 : y = (k y x) := by grind
  clear eq3627616
  have eq3630853 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq3629532
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3629532
    | exact resolve eq3629532 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3629532
  have eq3631180 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3627538 eq3630853
    | exact resolve eq3630853 eq3627538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3630853
  have eq3632701 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq85
       have i₂ := eq3629604
       grind)
    | exact superpose eq3629604 eq85
    | exact resolve eq85 eq3629604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq3629604
  have eq3632866 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq3627538 eq3632701
    | exact resolve eq3632701 eq3627538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3632701
  have eq3632916 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3632866
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq3632866
    | exact resolve eq3632866 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3632866
  have eq3633183 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3632916 eq11
    | (have j0 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq3632916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3632916
  have eq3633227 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3627648 eq3633183
    | exact resolve eq3633183 eq3627648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3633183
  have eq3633249 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3627648 eq3633227
    | exact resolve eq3633227 eq3627648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3633227
  have eq3633269 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq3633249
       have r₂ := eq28
       grind)
    | exact resolve eq3633249 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3633249
  have eq3663230 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3633269 eq30273
    | exact resolve eq30273 eq3633269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30273 eq3633269
  have eq3663455 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3627648 eq3663230
    | exact resolve eq3663230 eq3627648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3663230
  have eq3664015 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq3663455
       have r₂ := eq28
       grind)
    | exact resolve eq3663455 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3663455
  have eq3664645 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq3664015 eq28
    | exact resolve eq28 eq3664015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq4619026 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3631180 eq264763
    | exact resolve eq264763 eq3631180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264763
  have eq4619620 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3627648 eq4619026
    | exact resolve eq4619026 eq3627648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3627648 eq4619026
  have eq4619623 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3664015 eq4619620
    | exact resolve eq4619620 eq3664015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3664015 eq4619620
  have eq4619624 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq4619623
  have eq4619907 : (σ y) = (k (σ y) (σ y)) ∨ x = y := by grind
  clear eq4619624
  have eq4622314 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq4619907 eq3631180
    | exact resolve eq3631180 eq4619907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3631180 eq4619907
  have eq4622558 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq4622314
  have eq4622657 : x = y := by
    first
    | (have r₁ := eq4622558
       have r₂ := eq3664645
       grind)
    | exact resolve eq4622558 eq3664645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4622558
  have eq4622820 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq4622657
       grind)
    | exact superpose eq4622657 eq25
    | exact resolve eq25 eq4622657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq4622657
  have eq4624663 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq4622820
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq4622820
    | exact resolve eq4622820 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq4622820
  have eq4624968 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3627538 eq4624663
    | exact resolve eq4624663 eq3627538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3627538 eq4624663
  have eq4625130 : False := by grind
  exact eq4625130

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,X) else if m(X,X) = m(X,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_pxy_pxx_pyx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  clear eq35
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq24 eq36
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq81
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq81
    | exact resolve eq81 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq86
    | exact resolve eq86 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq90 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq88
    | exact resolve eq88 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq90
    | exact resolve eq90 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq102 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x y) ∨ (k x y) = (M.op y x) := by
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
  have eq110 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq112 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq112 x
       have r₂ := eq13 x x
       grind)
    | exact resolve eq112 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq116 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq113 x
       grind)
    | exact superpose eq113 eq43
    | exact resolve eq43 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq117 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq113 y
       grind)
    | exact superpose eq113 eq73
    | exact resolve eq73 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq120 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq117
       have i₂ := eq113 sF3
       grind)
    | exact superpose eq113 eq117
    | exact resolve eq117 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq121 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq116
       have i₂ := eq113 sF2
       grind)
    | exact superpose eq113 eq116
    | exact resolve eq116 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq126 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq102
       have i₂ := eq113 sF3
       grind)
    | exact superpose eq113 eq102
    | exact resolve eq102 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq127 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq126
       have i₂ := eq113 y
       grind)
    | exact superpose eq113 eq126
    | exact resolve eq126 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq126
  have eq252 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq50 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq252 eq50
    | exact resolve eq50 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq587 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq624 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq52 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1416 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq255 eq50
    | exact resolve eq50 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq1439 : (M.op (M.op x y) (M.op y (M.op x y))) = (M.op y (M.op y (M.op x y))) := by
    first
    | exact superpose eq252 eq1416
    | exact resolve eq1416 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1416
  have eq1827 : (M.op x y) = (M.op y (M.op y (M.op y (M.op x y)))) := by
    first
    | exact superpose eq1439 eq260
    | exact resolve eq260 eq1439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260 eq1439
  have eq1911 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0))
       have i₂ := eq624 X0 X0 X0
       grind)
    | exact superpose eq624 eq50
    | exact resolve eq50 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1912 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq624 X0 X0 X0
       grind)
    | exact superpose eq624 eq51
    | exact resolve eq51 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq2168 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq587 X0
       have i₂ := eq1911 X0
       grind)
    | exact superpose eq1911 eq587
    | exact resolve eq587 eq1911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq2194 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq51 sF4
       have i₂ := eq1911 sF4
       grind)
    | exact superpose eq1911 eq51
    | exact resolve eq51 eq1911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq2196 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1911 eq591
    | exact resolve eq591 eq1911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1911
  have eq2207 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq591 eq2196
    | exact resolve eq2196 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2196
  have eq2241 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq50 eq2168
    | exact resolve eq2168 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2168
  have eq2404 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1912 eq591
    | exact resolve eq591 eq1912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1912
  have eq2415 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq591 eq2404
    | exact resolve eq2404 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591 eq2404
  have eq17671 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq91 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17672 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq17671
    | exact resolve eq17671 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17671
  have eq17677 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17672
       have r₂ := eq27
       grind)
    | exact resolve eq17672 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17672
  have eq17679 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq17677
    | exact resolve eq17677 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17677
  have eq17681 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq17679
    | exact resolve eq17679 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17679
  have eq17683 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17681 eq110
    | (have r₁ := eq110
       have r₂ := eq17681
       grind)
    | exact resolve eq110 eq17681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq17687 : (σ x) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17681 eq50
    | exact resolve eq50 eq17681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17681
  have eq17763 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq17683
  have eq17764 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq17763
  have eq18225 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17687 eq2194
    | exact resolve eq2194 eq17687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2194 eq17687
  have eq18521 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17764 eq91
    | exact resolve eq91 eq17764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq17764
  have eq18531 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18521
  have eq18677 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18531 eq18225
    | exact resolve eq18225 eq18531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18225 eq18531
  have eq18711 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq18677
  have eq18718 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18711
       have r₂ := eq27
       grind)
    | exact resolve eq18711 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18711
  have eq18722 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (k x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq109
       have i₂ := eq18718
       grind)
    | exact superpose eq18718 eq109
    | (have r₁ := eq109
       have r₂ := eq18718
       grind)
    | exact resolve eq109 eq18718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq18723 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq121
       have i₂ := eq18718
       grind)
    | exact superpose eq18718 eq121
    | exact resolve eq121 eq18718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq18732 : x = (M.op y (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq18718
       grind)
    | exact superpose eq18718 eq50
    | exact resolve eq50 eq18718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq18718
  have eq18807 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (k x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18722
  have eq18808 : (k x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18807
  have eq18837 : x = (M.op y (M.op y (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq252 eq18732
    | exact resolve eq18732 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq18732
  have eq18843 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq18723
    | exact resolve eq18723 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18723
  have eq19898 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq18808
       grind)
    | exact superpose eq18808 eq44
    | exact resolve eq44 eq18808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq18808
  have eq20261 : (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18837 eq1827
    | exact resolve eq1827 eq18837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1827 eq18837
  have eq21012 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19898
       have i₂ := eq20261
       grind)
    | exact superpose eq20261 eq19898
    | exact resolve eq19898 eq20261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19898 eq20261
  have eq21061 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21012
  have eq21075 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq21061
    | exact resolve eq21061 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21061
  have eq21087 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21075 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq21075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21075
  have eq21090 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq21087
    | exact resolve eq21087 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21087
  have eq21095 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq21090
       have r₂ := eq27
       grind)
    | exact resolve eq21090 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21090
  have eq21097 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq21095
    | exact resolve eq21095 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21095
  have eq21099 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq21097
    | exact resolve eq21097 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21097
  have eq21100 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21099
  have eq21178 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21100 eq18843
    | exact resolve eq18843 eq21100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18843 eq21100
  have eq21261 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21178
  have eq21281 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq21261
       have r₂ := eq27
       grind)
    | exact resolve eq21261 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21261
  have eq21319 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21281 eq2415
    | exact resolve eq2415 eq21281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2415
  have eq21330 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq21319
    | exact resolve eq21319 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21319
  have eq21336 : (τ (M.op (σ x) (σ y))) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21330 eq127
    | exact resolve eq127 eq21330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq21330
  have eq21484 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2241 y
       have i₂ := eq21336
       grind)
    | exact superpose eq21336 eq2241
    | exact resolve eq2241 eq21336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21336
  have eq23690 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21281 eq21484
    | exact resolve eq21484 eq21281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21281 eq21484
  have eq23726 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ x = (M.op x y) := by grind
  clear eq23690
  have eq23734 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq23726
    | exact resolve eq23726 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq23726
  have eq23737 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23734
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23734
    | exact resolve eq23734 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23734
  have eq23738 : x = (M.op x y) := by grind
  clear eq23737
  have eq23833 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq23738 eq20
    | exact resolve eq20 eq23738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq23912 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq23738 eq2207
    | exact resolve eq2207 eq23738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2207
  have eq23937 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq23912
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23912
    | exact resolve eq23912 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq23912
  have eq23986 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq23833
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23833
    | exact resolve eq23833 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23833
  have eq23987 : x = (M.op y y) := by
    first
    | exact superpose eq23738 eq23937
    | exact resolve eq23937 eq23738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23738 eq23937
  have eq24035 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq23986 eq26
    | exact resolve eq26 eq23986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq24135 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq120
       have i₂ := eq23987
       grind)
    | exact superpose eq23987 eq120
    | exact resolve eq120 eq23987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq23987
  have eq24271 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq24135
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24135
    | exact resolve eq24135 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24135
  have eq24292 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq23986 eq24271
    | exact resolve eq24271 eq23986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23986 eq24271
  have eq24639 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq24292 eq2241
    | exact resolve eq2241 eq24292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2241 eq24292
  have eq24703 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24035 eq24639
    | exact resolve eq24639 eq24035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24035 eq24639
  have eq24727 : False := by grind
  exact eq24727

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,X) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pxy_y_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  clear eq22
  have eq62 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X2 X1) (M.op X0 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq9
    | exact resolve eq9 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (M.op (M.op x x) (M.op X0 X0)) x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq108 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X1 X1)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq70 X0 X0
       grind)
    | exact superpose eq70 eq70
    | exact resolve eq70 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X1 X1))
       have i₂ := eq70 X1 X0
       grind)
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq80 X0 (M.op X1 (M.op X1 X1))
       have i₂ := eq70 X1 X1
       grind)
    | exact superpose eq70 eq80
    | exact resolve eq80 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq70 X0 X0
       grind)
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq154 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq118 X2 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq118 X0 X0 X0
       grind)
    | exact superpose eq118 eq118
    | exact resolve eq118 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op X3 (M.op (M.op X4 X3) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq122 X2 X3 X4
       have i₂ := eq122 X2 X0 X1
       grind)
    | exact superpose eq122 eq122
    | exact resolve eq122 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq119 X2 X3
       have i₂ := eq122 X2 X0 X1
       grind)
    | exact superpose eq122 eq119
    | exact resolve eq119 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X2
       have i₂ := eq122 X2 X0 X1
       grind)
    | exact superpose eq122 eq65
    | exact resolve eq65 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq195 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X2)) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq118 X2 X3 X2
       have i₂ := eq122 X2 X0 X1
       grind)
    | exact superpose eq122 eq118
    | exact resolve eq118 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80 X2 X2
       have i₂ := eq122 X2 X0 X1
       grind)
    | exact superpose eq122 eq80
    | exact resolve eq80 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq201 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X3) X3 X2
       have i₂ := eq122 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq122 eq9
    | exact resolve eq9 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq285 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X0 X0)) (M.op X0 X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq193 (M.op X3 (M.op X0 X0)) (M.op x (M.op X3 X3)) X2 X1
       have i₂ := eq118 X3 x X0
       grind)
    | exact superpose eq118 eq193
    | exact resolve eq193 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq514 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq524 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq514 (σ X0)
       grind)
    | exact superpose eq514 eq15
    | exact resolve eq15 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq528 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq514 (τ X0)
       grind)
    | exact superpose eq514 eq18
    | exact resolve eq18 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq531 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq528 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq528
    | exact resolve eq528 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq535 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq524 X0
       have i₂ := eq514 X0
       grind)
    | exact superpose eq514 eq524
    | exact resolve eq524 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq539 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq531 X0
       have i₂ := eq514 X0
       grind)
    | exact superpose eq514 eq531
    | exact resolve eq531 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq555 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (M.op (M.op X2 X1) (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq535 X0
       grind)
    | exact superpose eq535 eq9
    | exact resolve eq9 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq577 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq539 X0
       grind)
    | exact superpose eq539 eq10
    | exact resolve eq10 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq592 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (M.op X1 (M.op (M.op X2 X1) (τ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq193 X1 X2 (τ X0) (τ X0)
       have i₂ := eq577 X0
       grind)
    | exact superpose eq577 eq193
    | exact resolve eq193 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq596 : ∀ X0 X1 X2 : G, (τ X0) = (M.op X1 (M.op (M.op X2 X1) (τ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (τ X0) X1 X2
       have i₂ := eq577 X0
       grind)
    | exact superpose eq577 eq9
    | exact resolve eq9 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq603 : ∀ X0 X1 X2 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (M.op X1 (M.op (M.op X2 X1) (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq122 (τ X0) X1 X2
       have i₂ := eq577 X0
       grind)
    | exact superpose eq577 eq122
    | exact resolve eq122 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq841 : ∀ X0 X1 X2 X3 : G, (σ (M.op X1 X0)) = (M.op X2 (M.op (M.op X3 X2) (σ (M.op X0 (M.op X1 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq555 (M.op X1 X0) X2 X3
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq555
    | exact resolve eq555 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1465 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq1474 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1465 X0 X1
       have i₂ := eq535 X0
       grind)
    | exact superpose eq535 eq1465
    | (have j0 := eq1465 X0 X1
       grind)
    | exact resolve eq1465 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465
  have eq2463 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) = (M.op X3 (M.op (M.op X4 X3) (M.op X0 (M.op (M.op X1 X0) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq67 X2 X2 X3 X4
       have i₂ := eq122 X2 X0 X1
       grind)
    | exact superpose eq122 eq67
    | exact resolve eq67 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2892 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op (M.op X3 (M.op X3 X3)) (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq108 X2 X3
       have i₂ := eq122 X2 X0 X1
       grind)
    | exact superpose eq122 eq108
    | exact resolve eq108 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq3045 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X3 X0) (M.op (M.op X0 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq193 (M.op X3 X0) (M.op X3 (M.op X3 X3)) X2 X1
       have i₂ := eq108 X0 X3
       grind)
    | exact superpose eq108 eq193
    | exact resolve eq193 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3051 : ∀ X0 X1 X2 : G, (τ X1) = (M.op (M.op X2 X0) (M.op (M.op X0 (M.op X0 X0)) (τ (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq596 X1 (M.op X2 X0) (M.op X2 (M.op X2 X2))
       have i₂ := eq108 X0 X2
       grind)
    | exact superpose eq108 eq596
    | exact resolve eq596 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq3905 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (M.op (σ X0) (σ X1)) (M.op X2 X2))) = X2 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X0) (σ X1)
       have i₂ := eq1474 X1 X0
       grind)
    | (have i₁ := eq9 X0 (σ X0) (σ X1)
       have i₂ := eq1474 X0 X1
       grind)
    | exact superpose eq1474 eq9
    | (have j1 := eq1474 X1 X0
       grind)
    | exact resolve eq9 eq1474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3928 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1474 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474
  have eq5103 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op (M.op X4 X0) (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq154 (M.op X1 (M.op (M.op X2 X1) X0)) X3 (M.op X4 X0)
       have i₂ := eq193 X1 X2 X0 X4
       grind)
    | exact superpose eq193 eq154
    | exact resolve eq154 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5400 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5103 X0 X1 X2 X3 X4
       have i₂ := eq62 X4 X0
       grind)
    | exact superpose eq62 eq5103
    | exact resolve eq5103 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5103
  have eq5508 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op (M.op X2 X1) X0) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5400 X0 X1 X2 X3 X4
       have i₂ := eq62 X1 (M.op (M.op X2 X1) X0)
       grind)
    | exact superpose eq62 eq5400
    | exact resolve eq5400 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5400
  have eq5557 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5508 X0 X1 X2 X3 X4
       have i₂ := eq193 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq193 eq5508
    | exact resolve eq5508 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5508
  have eq5579 : ∀ X0 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq5557 X0 x x X3 X4
       have i₂ := eq197 x x X0
       grind)
    | exact superpose eq197 eq5557
    | exact resolve eq5557 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq5557
  have eq5632 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0)))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5579 (M.op X1 X0) X2 (M.op x (M.op X1 X1))
       have i₂ := eq154 X0 x X1
       grind)
    | exact superpose eq154 eq5579
    | exact resolve eq5579 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5787 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5632 X0 X1 X2
       have i₂ := eq119 X0 X1
       grind)
    | exact superpose eq119 eq5632
    | exact resolve eq5632 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5632
  have eq5841 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5787 X0 X1 X2
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq5787
    | exact resolve eq5787 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq5787
  have eq8066 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) X0) = (M.op (M.op X1 (M.op (M.op (M.op X2 (M.op X3 X0)) X0) (M.op (M.op X2 (M.op X3 X0)) X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq195 X0 X3 (M.op (M.op X2 (M.op X3 X0)) X0) X1
       have i₂ := eq194 (M.op X3 X0) X2 X0
       grind)
    | exact superpose eq194 eq195
    | exact resolve eq195 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq8266 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) X0) = (M.op (M.op X1 (M.op X0 (M.op (M.op X2 (M.op X3 X0)) X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8066 X0 X1 X2 X3
       have i₂ := eq5841 X0 (M.op X2 (M.op X3 X0)) (M.op X2 (M.op X3 X0))
       grind)
    | exact superpose eq5841 eq8066
    | exact resolve eq8066 eq5841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8066
  have eq8344 : ∀ X0 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X2 (M.op X3 X0)) X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq8266 X0 x X2 X3
       have i₂ := eq5579 X0 x (M.op X2 (M.op X3 X0))
       grind)
    | exact superpose eq5579 eq8266
    | exact resolve eq8266 eq5579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5579 eq8266
  have eq9706 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq201 (M.op X1 X1) x X1 (M.op X0 X0)
       have i₂ := eq118 X1 x X0
       grind)
    | exact superpose eq118 eq201
    | exact resolve eq201 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq201
  have eq9847 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9706 X0 X1
       have i₂ := eq5841 X0 (M.op X1 X1) X0
       grind)
    | exact superpose eq5841 eq9706
    | exact resolve eq9706 eq5841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9706
  have eq9896 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9847 (M.op X1 X0) (M.op X1 X1)
       have i₂ := eq154 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq154 eq9847
    | exact resolve eq9847 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq10021 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X0 X0)) X2) (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq193 (M.op X0 X0) X1 X2 (M.op X1 (M.op X0 X0))
       have i₂ := eq9847 (M.op (M.op X1 (M.op X0 X0)) X2) X0
       grind)
    | exact superpose eq9847 eq193
    | exact resolve eq193 eq9847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9847
  have eq10053 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10021 X0 X1 X2
       have i₂ := eq5841 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq5841 eq10021
    | exact resolve eq10021 eq5841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10021
  have eq10125 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9896 X0 X1
       have i₂ := eq5841 X0 X1 X1
       grind)
    | exact superpose eq5841 eq9896
    | exact resolve eq9896 eq5841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9896
  have eq10186 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10125 X0 X1
       have i₂ := eq119 X0 X1
       grind)
    | exact superpose eq119 eq10125
    | exact resolve eq10125 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq10125
  have eq10317 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10186 (M.op (M.op X2 X1) X0) X1
       have i₂ := eq193 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq193 eq10186
    | exact resolve eq10186 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq10606 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10317 (M.op X0 (M.op X2 X0)) X2 X1
       have i₂ := eq10186 X0 X2
       grind)
    | exact superpose eq10186 eq10317
    | exact resolve eq10317 eq10186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10186 eq10317
  have eq12515 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq67 X0 (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X3 X2
       have i₂ := eq10053 (M.op X2 X3) X1 X0
       grind)
    | exact superpose eq10053 eq67
    | exact resolve eq67 eq10053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq10053
  have eq12552 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op X3 (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12515 X0 X1 X2 X3
       have i₂ := eq5841 X3 X2 X2
       grind)
    | exact superpose eq5841 eq12515
    | exact resolve eq12515 eq5841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12515
  have eq23489 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X0 X1)) (M.op (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq285 (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3 X4
       have i₂ := eq195 X1 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq195 eq285
    | exact resolve eq285 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq285
  have eq23874 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X0 X1)) (M.op (M.op X1 (M.op X1 (M.op X0 X1))) X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq23489 X0 X1 X2 X3 X4
       have i₂ := eq5841 X1 X0 X0
       grind)
    | exact superpose eq5841 eq23489
    | exact resolve eq23489 eq5841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5841 eq23489
  have eq23959 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X0 X1)) (M.op X1 X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq23874 X0 X1 X2 X3 X4
       have i₂ := eq12552 X3 X1 X0 X1
       grind)
    | exact superpose eq12552 eq23874
    | exact resolve eq23874 eq12552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12552 eq23874
  have eq38636 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X0) = (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq10606 (M.op X4 X0) X1 (M.op X2 (M.op X3 X4))
       have i₂ := eq23959 X3 X4 X4 X0 X2
       grind)
    | exact superpose eq23959 eq10606
    | exact resolve eq10606 eq23959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10606 eq23959
  have eq128160 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op X0 (M.op (M.op X1 X0) (τ X2)))) = (M.op X3 (M.op (M.op X4 X3) (σ (M.op (τ (M.op X2 X2)) (M.op X0 (M.op (M.op X1 X0) (τ X2))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq841 (τ (M.op X0 X0)) (τ X0) X2 X3
       have i₂ := eq603 X0 X1 X2
       grind)
    | exact superpose eq603 eq841
    | exact resolve eq841 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603 eq841
  have eq128639 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op X0 (M.op (M.op X1 X0) (τ X2)))) = (M.op X3 (M.op (M.op X4 X3) (σ (τ X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq128160 X0 X1 X2 X3 X4
       have i₂ := eq592 X2 X0 X1
       grind)
    | exact superpose eq592 eq128160
    | exact resolve eq128160 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592 eq128160
  have eq128848 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X4 X3) X2)) = (σ (M.op X0 (M.op (M.op X1 X0) (τ X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq128639 X0 X1 X2 X3 X4
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq128639
    | exact resolve eq128639 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128639
  have eq142096 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X6 X6) = (M.op X5 (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6)))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq2463 (M.op X3 (M.op X4 X5)) X2 X6 X5 X4
       have i₂ := eq179 (M.op X4 X5) X3 (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6) X0 X1
       grind)
    | (have i₁ := eq2463 (M.op X3 (M.op X4 X5)) X2 X6 X5 X4
       have i₂ := eq179 X0 X1 (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6) (M.op X4 X5) X3
       grind)
    | exact superpose eq179 eq2463
    | exact resolve eq2463 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq143209 : ∀ X0 X1 X5 X6 : G, (M.op X6 X6) = (M.op X5 (M.op X0 (M.op (M.op X1 X0) (M.op X5 X6)))) := by
    intro X0 X1 X5 X6
    first
    | (have i₁ := eq142096 X0 X1 x x x X5 X6
       have i₂ := eq38636 X6 x x x X5
       grind)
    | exact superpose eq38636 eq142096
    | exact resolve eq142096 eq38636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142096
  have eq144616 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))) ≠ (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))) ∨ (k X3 X3) = (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 x x
       have i₂ := eq143209 X0 X1 x x
       grind)
    | exact superpose eq143209 eq12
    | (have r₁ := eq12 (M.op X0 (M.op (M.op X1 X0) (M.op x x))) x
       have r₂ := eq143209 X0 X1 x x
       grind)
    | exact resolve eq12 eq143209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143209
  have eq145142 : ∀ X0 X1 X2 X3 : G, (k X3 X3) = (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq144616 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144616
  have eq146881 : ∀ X0 X1 X2 X3 : G, (τ (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 (σ X3)))))) = (k X3 (τ (σ X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq28 X3 (σ X3)
       have i₂ := eq145142 X0 X1 X2 (σ X3)
       grind)
    | exact superpose eq145142 eq28
    | exact resolve eq28 eq145142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq145142
  have eq147428 : ∀ X0 X1 X2 X3 : G, (k X3 X3) = (τ (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 (σ X3)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq146881 X0 X1 X2 X3
       have i₂ := eq10 X3
       grind)
    | exact superpose eq10 eq146881
    | exact resolve eq146881 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146881
  have eq149676 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X5 X5) = (M.op X4 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X5)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq2463 (M.op X2 (M.op X3 X4)) X1 X5 X4 X3
       have i₂ := eq2892 (M.op X3 X4) X2 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X5) X0
       grind)
    | exact superpose eq2892 eq2463
    | exact resolve eq2463 eq2892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2463 eq2892
  have eq150471 : ∀ X0 X4 X5 : G, (M.op X5 X5) = (M.op X4 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X4 X5)))) := by
    intro X0 X4 X5
    first
    | (have i₁ := eq149676 X0 x x x X4 X5
       have i₂ := eq38636 X5 x x x X4
       grind)
    | exact superpose eq38636 eq149676
    | exact resolve eq149676 eq38636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149676
  have eq321205 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X4) (M.op (M.op X5 X2) (M.op (M.op X2 (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X0 X2))))) X4))) = X4 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq3045 X2 X3 X4 X5
       have i₂ := eq150471 X1 X0 X2
       grind)
    | exact superpose eq150471 eq3045
    | exact resolve eq3045 eq150471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3045
  have eq321208 : ∀ X0 X1 X2 X3 X4 : G, (τ X3) = (M.op (M.op X4 X2) (M.op (M.op X2 (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X0 X2))))) (τ (M.op X3 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3051 X2 X3 X4
       have i₂ := eq150471 X1 X0 X2
       grind)
    | exact superpose eq150471 eq3051
    | exact resolve eq3051 eq150471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3051 eq150471
  have eq322852 : ∀ X0 X1 X2 X3 X4 : G, (τ X3) = (M.op (M.op X4 X2) (M.op (M.op X1 (M.op X0 X2)) (τ (M.op X3 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq321208 X0 X1 X2 X3 X4
       have i₂ := eq38636 (τ (M.op X3 X3)) X2 X0 (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X0 X2))
       grind)
    | exact superpose eq38636 eq321208
    | exact resolve eq321208 eq38636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321208
  have eq322854 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X4) (M.op (M.op X5 X2) (M.op (M.op X1 (M.op X0 X2)) X4))) = X4 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq321205 X0 X1 X2 X3 X4 X5
       have i₂ := eq38636 X4 X2 X0 (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X0 X2))
       grind)
    | exact superpose eq38636 eq321205
    | exact resolve eq321205 eq38636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38636 eq321205
  have eq730570 : ∀ X0 X1 X2 X3 : G, (M.op (σ X1) (σ X0)) = (M.op (M.op X2 (M.op X3 (σ X0))) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3905 X1 X0 (M.op (M.op X2 (M.op X3 (σ X0))) (σ X0))
       have i₂ := eq322854 X3 X2 (σ X0) (σ X1) (σ X0) (M.op X2 (M.op X3 (σ X0)))
       grind)
    | exact superpose eq322854 eq3905
    | (have j0 := eq3905 X1 X0 X2
       grind)
    | exact resolve eq3905 eq322854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3905 eq322854
  have eq731349 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq730570 X0 X1 x x
       have i₂ := eq8344 (σ X0) x x
       grind)
    | exact superpose eq8344 eq730570
    | (have j0 := eq730570 X0 X1 x x
       grind)
    | exact resolve eq730570 eq8344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8344 eq730570
  have eq732461 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq731349 X0 X1
       have i₂ := eq535 X0
       grind)
    | exact superpose eq535 eq731349
    | (have j0 := eq731349 X0 X1
       grind)
    | exact resolve eq731349 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731349
  have eq732874 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq732461 X0 X1
       have j1 := eq3928 X0 X1
       grind)
    | (have r₁ := eq732461 X0 X1
       have r₂ := eq3928 X0 X1
       grind)
    | (have r₁ := eq732461 X1 X1
       have r₂ := eq3928 X1 X1
       grind)
    | exact resolve eq732461 eq3928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3928 eq732461
  have eq737818 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq732874 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732874
  have eq739037 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq737818 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737818
  have eq739722 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X3 X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq739037 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739037
  have eq743976 : ∀ X5 X6 : G, (M.op (σ X5) (σ X6)) = (σ (k X6 X5)) ∨ (σ (M.op X5 X5)) = (M.op (σ X5) (σ X6)) := by
    intro X5 X6
    first
    | (have j0 := eq739722 X5 X6
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739722
  have eq745364 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq743976 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743976
  have eq746051 : ∀ X1 X2 : G, (M.op (σ X2) (σ X1)) = (σ (k X1 X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq745364 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745364
  have eq749790 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq746051 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746051
  have eq754261 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq749790 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749790
  have eq754675 : ∀ X1 X2 : G, (M.op (σ X2) (σ X1)) = (σ (k X1 X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq754261 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754261
  have eq756295 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq754675 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754675
  have eq758801 : ∀ X2 X3 : G, (M.op (σ X3) (σ X2)) = (σ (k X2 X3)) ∨ (σ (M.op X3 X3)) = (M.op (σ X3) (σ X2)) := by
    intro X2 X3
    first
    | (have j0 := eq756295 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756295
  have eq765612 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X4 X3)) ∨ (σ (M.op X3 X3)) = (M.op (σ X3) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq758801 X4 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758801
  have eq772724 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq765612 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765612
  have eq774890 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq772724 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772724
  have eq777073 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq774890 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774890
  have eq779026 : ∀ X1 X2 : G, (M.op (σ X2) (σ X1)) = (σ (k X1 X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq777073 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777073
  have eq789373 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq779026 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779026
  have eq790041 : ∀ X1 X5 : G, (M.op (σ X5) (σ X1)) = (σ (k X1 X5)) ∨ (σ (M.op X5 X5)) = (M.op (σ X5) (σ X1)) := by
    intro X1 X5
    first
    | (have j0 := eq789373 X5 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789373
  have eq792052 : ∀ X4 X5 : G, (M.op (σ X5) (σ X4)) = (σ (k X4 X5)) ∨ (σ (M.op X5 X5)) = (M.op (σ X5) (σ X4)) := by
    intro X4 X5
    first
    | (have j0 := eq790041 X4 X5
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790041
  have eq792547 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq792052 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792052
  have eq794649 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq792547 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792547
  have eq796053 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq794649 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794649
  have eq796682 : ∀ X1 X3 : G, (M.op (σ X3) (σ X1)) = (σ (k X1 X3)) ∨ (σ (M.op X3 X3)) = (M.op (σ X3) (σ X1)) := by
    intro X1 X3
    first
    | (have j0 := eq796053 X1 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796053
  have eq799638 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq796682 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796682
  have eq802051 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq799638 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799638
  have eq804071 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq802051 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802051
  have eq806240 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq804071 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804071
  have eq808288 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq806240 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806240
  have eq809904 : ∀ X1 X2 : G, (M.op (σ X2) (σ X1)) = (σ (k X1 X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq808288 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808288
  have eq813053 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq809904 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809904
  have eq814928 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq813053 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813053
  have eq817278 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq814928 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814928
  have eq820060 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq817278 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817278
  have eq820640 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq820060 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820060
  have eq823234 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq820640 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820640
  have eq825771 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq823234 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823234
  have eq836781 : ∀ X2 X3 : G, (M.op (σ X3) (σ X2)) = (σ (k X2 X3)) ∨ (σ (M.op X3 X3)) = (M.op (σ X3) (σ X2)) := by
    intro X2 X3
    first
    | (have j0 := eq825771 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825771
  have eq841141 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq836781 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836781
  have eq842418 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq841141 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841141
  have eq842974 : ∀ X3 X4 : G, (M.op (σ X4) (σ X3)) = (σ (k X3 X4)) ∨ (σ (M.op X4 X4)) = (M.op (σ X4) (σ X3)) := by
    intro X3 X4
    first
    | (have j0 := eq842418 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842418
  have eq843824 : ∀ X1 X2 : G, (σ (M.op X1 X1)) = (M.op (σ X1) (σ X2)) ∨ (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) := by
    intro X1 X2
    first
    | (have j0 := eq842974 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842974
  have eq867791 : ∀ X0 X1 X2 X3 : G, (k X1 X1) = (τ (M.op (σ X0) (M.op X2 (M.op (M.op X3 X2) (σ (M.op X0 X0)))))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq147428 (σ X0) X2 X3 X1
       have i₂ := eq843824 X0 X1
       grind)
    | exact superpose eq843824 eq147428
    | (have j1 := eq843824 X0 X1
       grind)
    | exact resolve eq147428 eq843824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147428 eq843824
  have eq868716 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X1 X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq867791 X0 X1 x x
       have i₂ := eq555 X0 x x
       grind)
    | exact superpose eq555 eq867791
    | (have j0 := eq867791 X0 X1 x x
       grind)
    | exact resolve eq867791 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555 eq867791
  have eq869173 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq868716 X0 X1
       have i₂ := eq514 X1
       grind)
    | exact superpose eq514 eq868716
    | (have j0 := eq868716 X0 X1
       grind)
    | exact resolve eq868716 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514 eq868716
  have eq869492 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq869173 X0 X1
       have i₂ := eq535 X0
       grind)
    | exact superpose eq535 eq869173
    | (have j0 := eq869173 X0 X1
       grind)
    | exact resolve eq869173 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869173
  have eq869642 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq869492 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq869492
    | (have j0 := eq869492 X0 X1
       grind)
    | exact resolve eq869492 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869492
  have eq1038394 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq869642 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq869642
    | (have j0 := eq869642 (τ X0) (τ X1)
       grind)
    | exact resolve eq869642 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq869642
  have eq1038689 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1038394 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1038394
    | (have j0 := eq1038394 X0 X1
       grind)
    | exact resolve eq1038394 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038394
  have eq1038724 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1038689 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1038689
    | (have j0 := eq1038689 X0 X1
       grind)
    | exact resolve eq1038689 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038689
  have eq1038745 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1038724 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1038724
    | (have j0 := eq1038724 X0 X1
       grind)
    | exact resolve eq1038724 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038724
  have eq1038760 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X1 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1038745 X0 X1
       have i₂ := eq577 X1
       grind)
    | exact superpose eq577 eq1038745
    | (have j0 := eq1038745 X0 X1
       grind)
    | exact resolve eq1038745 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038745
  have eq1038766 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (M.op X1 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1038760 X0 X1
       have i₂ := eq577 X0
       grind)
    | exact superpose eq577 eq1038760
    | (have j0 := eq1038760 X0 X1
       grind)
    | exact resolve eq1038760 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577 eq1038760
  have eq1039290 : ∀ X0 X1 X2 X3 X4 X5 : G, (τ X1) = (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X5 X3)) (τ (M.op X0 X0)))) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq322852 X5 X4 X3 X1 X2
       have i₂ := eq1038766 X0 X1
       grind)
    | (have i₁ := eq322852 X0 X1 X2 X0 X4
       have i₂ := eq1038766 X0 X1
       grind)
    | exact superpose eq1038766 eq322852
    | (have j1 := eq1038766 X0 X1
       grind)
    | exact resolve eq322852 eq1038766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1039433 : ∀ X0 X1 X2 X3 X4 X5 : G, (σ (M.op X4 (M.op (M.op X5 X4) (τ (M.op X0 X0))))) = (M.op X1 (M.op (M.op X2 X1) (M.op X3 X3))) ∨ (M.op X3 X0) = (k X0 X3) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq128848 X4 X5 (M.op X3 X3) X1 X2
       have i₂ := eq1038766 X0 X3
       grind)
    | (have i₁ := eq128848 X0 X1 (M.op X0 X0) X3 X4
       have i₂ := eq1038766 X0 X1
       grind)
    | exact superpose eq1038766 eq128848
    | (have j1 := eq1038766 X0 X3
       grind)
    | exact resolve eq128848 eq1038766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128848 eq1038766
  have eq1039519 : ∀ X0 X3 X4 X5 : G, (σ (M.op X4 (M.op (M.op X5 X4) (τ (M.op X0 X0))))) = X3 ∨ (M.op X3 X0) = (k X0 X3) := by
    intro X0 X3 X4 X5
    first
    | (have i₁ := eq1039433 X0 x x X3 X4 X5
       have i₂ := eq9 X3 x x
       grind)
    | exact superpose eq9 eq1039433
    | (have j0 := eq1039433 X0 x x X3 X4 X5
       grind)
    | exact resolve eq1039433 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039433
  have eq1039649 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1039290 X0 X1 x x x x
       have i₂ := eq322852 x x x X0 x
       grind)
    | exact superpose eq322852 eq1039290
    | (have j0 := eq1039290 X0 X1 x x x x
       grind)
    | exact resolve eq1039290 eq322852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322852 eq1039290
  have eq1039969 : ∀ X0 X3 : G, (σ (τ X0)) = X3 ∨ (M.op X3 X0) = (k X0 X3) := by
    intro X0 X3
    first
    | (have i₁ := eq1039519 X0 X3 x x
       have i₂ := eq596 X0 x x
       grind)
    | exact superpose eq596 eq1039519
    | (have j0 := eq1039519 X0 X3 x x
       grind)
    | exact resolve eq1039519 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596 eq1039519
  have eq1040156 : ∀ X0 X3 : G, (M.op X3 X0) = (k X0 X3) ∨ X0 = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq1039969 X0 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1039969
    | (have j0 := eq1039969 X0 X3
       grind)
    | exact resolve eq1039969 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039969
  have eq1040517 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1039649 (σ X1) (σ X0)
       grind)
    | exact superpose eq1039649 eq15
    | (have j1 := eq1039649 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq1039649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039649
  have eq1040622 : ∀ X0 X1 : G, (τ (σ X0)) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1040517 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1040517
    | (have j0 := eq1040517 X0 X1
       grind)
    | exact resolve eq1040517 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040517
  have eq1040729 : ∀ X0 X1 : G, X0 = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1040622 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1040622
    | (have j0 := eq1040622 X0 X1
       grind)
    | exact resolve eq1040622 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040622
  have eq1040809 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | exact superpose eq1040156 eq1040729
    | (have j0 := eq1040729 (σ (M.op X0 X1)) (M.op (σ X0) (σ X1))
       have j1 := eq1040156 (σ (M.op X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq1040729 eq1040156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040156 eq1040729
  have eq1044037 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1040809 x y
       grind)
    | exact superpose eq1040809 eq16
    | (have j1 := eq1040809 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1040809 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1040809 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq1040809 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq1040809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040809
  have eq1044413 : x = y := by grind
  clear eq1044037
  have eq1044609 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1044413
       grind)
    | exact superpose eq1044413 eq16
    | exact resolve eq16 eq1044413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044413
  have eq1044610 : False := by grind
  exact eq1044610

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(Y,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pxy_pyx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq66 (σ X0)
       grind)
    | exact superpose eq66 eq10
    | exact resolve eq10 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq68
    | exact resolve eq68 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq77 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq77 x y
       grind)
    | exact superpose eq77 eq44
    | (have j1 := eq77 x y
       grind)
    | exact resolve eq44 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq88
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq88
    | exact resolve eq88 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq95
    | exact resolve eq95 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq104 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq108 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq66 sF3
       grind)
    | exact superpose eq66 eq104
    | exact resolve eq104 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq110 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq66 y
       grind)
    | exact superpose eq66 eq108
    | exact resolve eq108 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq148 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq151 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq148
       have i₂ := eq66 sF1
       grind)
    | exact superpose eq66 eq148
    | exact resolve eq148 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq153 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq151
       have i₂ := eq66 sF0
       grind)
    | exact superpose eq66 eq151
    | exact resolve eq151 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq239 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq50 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq51 (M.op sF4 sF4)
       have i₂ := eq14 sF4 sF4 sF4
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : (σ (M.op y (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq239 eq153
    | exact resolve eq153 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq239
  have eq288 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq66 (τ X0)
       grind)
    | exact superpose eq66 eq34
    | exact resolve eq34 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq299 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq288 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq288
    | exact resolve eq288 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq302 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq299 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq299
    | exact resolve eq299 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq299
  have eq504 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq510 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X3
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0) (σ X0)
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq14
    | exact resolve eq14 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq710 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq52 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq735 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq746 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq53 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq52 X0 x x X3
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq751 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq752 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq50
    | exact resolve eq50 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq753 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq756 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq753 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq753
    | exact resolve eq753 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq757 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq752 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq752
    | exact resolve eq752 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq758 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq751 X0 X1 X2 X3
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq751
    | exact resolve eq751 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq812 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq302 X0
       grind)
    | exact superpose eq302 eq16
    | exact resolve eq16 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq993 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq97 eq77
    | (have j0 := eq77 (σ x) (σ y)
       grind)
    | exact resolve eq77 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq994 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq993
    | exact resolve eq993 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993
  have eq997 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq994
       have r₂ := eq27
       grind)
    | exact resolve eq994 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994
  have eq1000 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq997 eq53
    | exact resolve eq53 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1001 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq997 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq997
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq997
       grind)
    | exact resolve eq12 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1002 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op X0 X0))) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq997 eq14
    | exact resolve eq14 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1003 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq1001
  have eq1004 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq1000
    | exact resolve eq1000 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000
  have eq1112 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1004 eq1002
    | exact resolve eq1002 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002 eq1004
  have eq1120 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op y x) := by grind
  clear eq1112
  have eq1756 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1003 eq97
    | exact resolve eq97 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003
  have eq1759 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1756
  have eq1814 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0))
       have i₂ := eq710 X0 X0 X0
       grind)
    | exact superpose eq710 eq50
    | exact resolve eq50 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1815 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq710 X0 X0 X0
       grind)
    | exact superpose eq710 eq51
    | exact resolve eq51 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1826 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq746 (M.op x (M.op x x)) x
       have i₂ := eq710 x x x
       grind)
    | exact superpose eq710 eq746
    | exact resolve eq746 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1876 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1759 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | exact resolve eq13 eq1759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1759
  have eq1906 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq1876 X0
       have j1 := eq77 X0 (σ y)
       grind)
    | (have r₁ := eq1876 X0
       have r₂ := eq77 X0 (σ y)
       grind)
    | exact resolve eq1876 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq1876
  have eq4825 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1906 eq97
    | exact resolve eq97 eq1906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq1906
  have eq4837 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq4825
  have eq4847 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq4837
    | exact resolve eq4837 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4837
  have eq4849 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq4847
       have r₂ := eq27
       grind)
    | exact resolve eq4847 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4847
  have eq4852 : ∀ X0 : G, (M.op x (M.op y (M.op X0 X0))) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq4849
       grind)
    | exact superpose eq4849 eq14
    | exact resolve eq14 eq4849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4854 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq4849
       grind)
    | exact superpose eq4849 eq53
    | exact resolve eq53 eq4849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4863 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq4854
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4854
    | exact resolve eq4854 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4854
  have eq4867 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq110
       have i₂ := eq4863
       grind)
    | exact superpose eq4863 eq110
    | exact resolve eq110 eq4863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq4863
  have eq4906 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq4867
    | exact resolve eq4867 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4867
  have eq4933 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq4906 eq746
    | exact resolve eq746 eq4906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746 eq4906
  have eq5333 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x (M.op y X0)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq4852 (M.op X0 (M.op X0 X0))
       have i₂ := eq710 X0 X0 X0
       grind)
    | exact superpose eq710 eq4852
    | exact resolve eq4852 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710 eq4852
  have eq7214 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq510 X1 X0 X1 X0
       have i₂ := eq756 X0 X1
       grind)
    | exact superpose eq756 eq510
    | exact resolve eq510 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq7357 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq757 X0 X1
       have i₂ := eq756 X0 X1
       grind)
    | exact superpose eq756 eq757
    | exact resolve eq757 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq7386 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq7357 x (M.op (M.op x x) (M.op X0 X0))
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq7357
    | exact resolve eq7357 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7556 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq7357 (M.op x sF4) (M.op X0 X0)
       have i₂ := eq14 X0 sF4 x
       grind)
    | exact superpose eq14 eq7357
    | exact resolve eq7357 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9080 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq758 X0 X1 X2 X3
       have i₂ := eq756 X0 X1
       grind)
    | exact superpose eq756 eq758
    | exact resolve eq758 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq9081 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq7357 eq9080
    | exact resolve eq9080 eq7357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9080
  have eq9526 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X1 X0))) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9081 X1 X0 X0 X1
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq9081
    | exact resolve eq9081 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29654 : ∀ X0 X1 X2 : G, (M.op y x) = (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X2 (M.op x (M.op x x)))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq735 x y X0 X1 X2
       have i₂ := eq5333 x
       grind)
    | exact superpose eq5333 eq735
    | exact resolve eq735 eq5333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5333
  have eq29754 : (M.op x x) = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq29654 x x x
       have i₂ := eq735 x x x x x
       grind)
    | exact superpose eq735 eq29654
    | exact resolve eq29654 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735 eq29654
  have eq29836 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq4849
       have i₂ := eq29754
       grind)
    | exact superpose eq29754 eq4849
    | exact resolve eq4849 eq29754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4849 eq29754
  have eq29885 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq29836
  have eq29972 : x = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1826 x x
       have i₂ := eq29885
       grind)
    | exact superpose eq29885 eq1826
    | exact resolve eq1826 eq29885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29885
  have eq30002 : x = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq29972
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq29972
    | exact resolve eq29972 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29972
  have eq30066 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq30002 eq247
    | exact resolve eq247 eq30002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30002
  have eq30206 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq30066
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30066
    | exact resolve eq30066 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30066
  have eq30578 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq30206 eq4933
    | exact resolve eq4933 eq30206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4933 eq30206
  have eq30689 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq30578
  have eq30724 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq30689
    | exact resolve eq30689 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30689
  have eq30732 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq30724
       have r₂ := eq27
       grind)
    | exact resolve eq30724 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30724
  have eq30734 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq30732 eq26
    | exact resolve eq26 eq30732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq30735 : y = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq30732 eq29
    | exact resolve eq29 eq30732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq30738 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq30732 eq51
    | exact resolve eq51 eq30732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq30756 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30732 eq997
    | exact resolve eq997 eq30732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997
  have eq30768 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30732 eq1120
    | exact resolve eq1120 eq30732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq30783 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq30732 eq1815
    | exact resolve eq1815 eq30732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1815
  have eq30797 : ∀ X0 : G, (M.op y (M.op (M.op x y) X0)) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq30732 eq7386
    | exact resolve eq7386 eq30732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7386
  have eq30836 : y = (M.op x y) := by
    first
    | exact superpose eq30 eq30735
    | exact resolve eq30735 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30735
  have eq31113 : ∀ X0 : G, (τ X0) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq30738 (τ X0)
       have i₂ := eq812 X0
       grind)
    | exact superpose eq812 eq30738
    | exact resolve eq30738 eq812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812 eq30738
  have eq33347 : ∀ X0 : G, (M.op X0 (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq504 X0
       have i₂ := eq30783 X0
       grind)
    | exact superpose eq30783 eq504
    | exact resolve eq504 eq30783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33355 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1826 X0 X1
       have i₂ := eq30783 X0
       grind)
    | exact superpose eq30783 eq1826
    | exact resolve eq1826 eq30783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1826 eq30783
  have eq34010 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq30836 eq30797
    | exact resolve eq30797 eq30836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30797
  have eq34257 : ∀ X0 : G, (M.op X0 (M.op y (M.op y X0))) = X0 := by
    intro X0
    first
    | exact superpose eq34010 eq33347
    | exact resolve eq33347 eq34010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33347
  have eq35203 : ∀ X0 : G, (τ X0) = (M.op y (M.op y (τ (M.op X0 X0)))) := by
    intro X0
    first
    | exact superpose eq34010 eq31113
    | exact resolve eq31113 eq34010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31113
  have eq35283 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op y (M.op y X0))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq34010 eq33355
    | exact resolve eq33355 eq34010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33355 eq34010
  have eq35666 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq34257 (τ (M.op X0 X0))
       have i₂ := eq35203 X0
       grind)
    | exact superpose eq35203 eq34257
    | exact resolve eq34257 eq35203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34257 eq35203
  have eq41333 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9081 (σ X0) (M.op (σ (M.op X0 X0)) (M.op X1 X1)) X2 x
       have i₂ := eq588 X0 X1
       grind)
    | exact superpose eq588 eq9081
    | exact resolve eq9081 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588 eq9081
  have eq41349 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op y (M.op y X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq30836 eq41333
    | exact resolve eq41333 eq30836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41333
  have eq47036 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op X1 X0) X0))) = (M.op (M.op (M.op X1 X0) X0) (M.op y (M.op y X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq756 (M.op X1 X0) X0
       have i₂ := eq41349 X0 X0 X1
       grind)
    | exact superpose eq41349 eq756
    | exact resolve eq756 eq41349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756 eq41349
  have eq47200 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op X1 X0) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq47036 X0 X1
       have i₂ := eq35283 X0 (M.op X1 X0)
       grind)
    | exact superpose eq35283 eq47036
    | exact resolve eq47036 eq35283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35283 eq47036
  have eq47334 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op (M.op X1 X0) X0))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq7357 eq47200
    | exact resolve eq47200 eq7357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47200
  have eq47384 : ∀ X0 X1 : G, (M.op y (M.op y (M.op (M.op X1 X0) X0))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq30836 eq47334
    | exact resolve eq47334 eq30836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47334
  have eq53132 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op y (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | exact superpose eq7357 eq7214
    | exact resolve eq7214 eq7357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7214 eq7357
  have eq53133 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op y (M.op y (M.op X0 X1)))) := by
    intro X0 X1
    first
    | exact superpose eq30836 eq53132
    | exact resolve eq53132 eq30836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53132
  have eq53141 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op y (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq53133 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq504 X0
       grind)
    | exact superpose eq504 eq53133
    | exact resolve eq53133 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504 eq53133
  have eq91718 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op y (M.op y (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq30836 eq7556
    | exact resolve eq7556 eq30836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7556
  have eq91719 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) X0) = (M.op y (M.op y (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq30732 eq91718
    | exact resolve eq91718 eq30732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91718
  have eq91833 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 X0)) = (M.op (M.op (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 X0)) (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 X0)))) (M.op (σ (M.op x y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq91719 eq53141
    | exact resolve eq53141 eq91719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53141
  have eq91944 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 X0)) = (M.op (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 X0)))) (M.op (σ (M.op x y)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq91833 X0 X1
       have i₂ := eq1814 (M.op (M.op X1 sF4) (M.op X0 X0))
       grind)
    | exact superpose eq1814 eq91833
    | exact resolve eq91833 eq1814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1814 eq91833
  have eq91998 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 X0)) = (M.op (M.op y (M.op y (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 X0)))) (M.op (σ (M.op x y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq30836 eq91944
    | exact resolve eq91944 eq30836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91944
  have eq92029 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 X0)) = (M.op (M.op (σ (M.op x y)) X0) (M.op (σ (M.op x y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq91719 eq91998
    | exact resolve eq91998 eq91719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91719 eq91998
  have eq92039 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 X0)) = (M.op X0 (M.op (σ (M.op x y)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq92029 X1 X1
       have i₂ := eq53 sF1 X1
       grind)
    | exact superpose eq53 eq92029
    | exact resolve eq92029 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq92029
  have eq96071 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = (M.op y (M.op y (M.op X1 X0))) := by
    intro X0 X1
    first
    | exact superpose eq30836 eq9526
    | exact resolve eq9526 eq30836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9526
  have eq96291 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ (M.op x y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq92039 eq14
    | exact resolve eq14 eq92039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92039
  have eq97376 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ (M.op x y)))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30756 eq96291
    | exact resolve eq96291 eq30756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30756 eq96291
  have eq97550 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30734 eq97376
    | exact resolve eq97376 eq30734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97376
  have eq97587 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq243 eq97550
    | exact resolve eq97550 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243 eq97550
  have eq97605 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30732 eq97587
    | exact resolve eq97587 eq30732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97587
  have eq99972 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq97605 eq30768
    | exact resolve eq30768 eq97605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30768 eq97605
  have eq100092 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq99972
  have eq101491 : (τ (σ (M.op x y))) = (M.op (τ (σ (M.op x y))) (τ (σ x))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq100092 eq35666
    | exact resolve eq35666 eq100092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35666 eq100092
  have eq101655 : (τ (σ (M.op x y))) = (M.op (τ (σ (M.op x y))) x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq28 eq101491
    | exact resolve eq101491 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq101491
  have eq101729 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30 eq101655
    | exact resolve eq101655 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq101655
  have eq101771 : y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30836 eq101729
    | exact resolve eq101729 eq30836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101729
  have eq101772 : y = (M.op y x) := by grind
  clear eq101771
  have eq101889 : x = (M.op y (M.op y (M.op y x))) := by
    first
    | (have i₁ := eq47384 x y
       have i₂ := eq101772
       grind)
    | exact superpose eq101772 eq47384
    | exact resolve eq47384 eq101772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47384
  have eq101906 : x = (M.op x (M.op x (M.op y x))) := by
    first
    | (have i₁ := eq101889
       have i₂ := eq96071 x y
       grind)
    | exact superpose eq96071 eq101889
    | exact resolve eq101889 eq96071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96071 eq101889
  have eq101950 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq101906
       have i₂ := eq101772
       grind)
    | exact superpose eq101772 eq101906
    | exact resolve eq101906 eq101772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101772 eq101906
  have eq101979 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq101950
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq101950
    | exact resolve eq101950 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101950
  have eq101998 : x = (M.op x y) := by
    first
    | exact superpose eq30836 eq101979
    | exact resolve eq101979 eq30836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101979
  have eq102007 : x = (M.op x y) := by
    first
    | (have i₁ := eq101998
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq101998
    | exact resolve eq101998 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101998
  have eq102009 : x = y := by
    first
    | exact superpose eq30836 eq102007
    | exact resolve eq102007 eq30836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102007
  have eq102013 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq102009
       grind)
    | exact superpose eq102009 eq24
    | exact resolve eq24 eq102009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq102024 : (σ (M.op x (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq247
       have i₂ := eq102009
       grind)
    | exact superpose eq102009 eq247
    | exact resolve eq247 eq102009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq102009
  have eq102382 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq30836 eq102024
    | exact resolve eq102024 eq30836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30836 eq102024
  have eq102393 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq30732 eq102013
    | exact resolve eq102013 eq30732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30732 eq102013
  have eq102449 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq102382
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102382
    | exact resolve eq102382 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq102382
  have eq102460 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq102393
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq102393
    | exact resolve eq102393 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq102393
  have eq102484 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq102449
    | exact resolve eq102449 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq102449
  have eq102549 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq102460 eq30734
    | exact resolve eq30734 eq102460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30734 eq102460
  have eq105062 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq102484 eq102549
    | exact resolve eq102549 eq102484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102484 eq102549
  have eq105063 : False := by grind
  exact eq105063
