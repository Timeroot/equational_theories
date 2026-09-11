import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_x_pyx_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 : G, (k (τ (σ X0)) X0) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq12 (τ (σ X0)) X0
       grind)
    | (have r₁ := eq12 (τ (σ X0)) X0
       have r₂ := eq10 X0
       grind)
    | (have r₁ := eq12 X0 (τ (σ X0))
       have r₂ := eq10 X0
       grind)
    | exact resolve eq12 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq17 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17
    | exact resolve eq17 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq28 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq15
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq37
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq46 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (τ X0)
       have i₂ := eq22 (τ X0)
       grind)
    | exact superpose eq22 eq28
    | exact resolve eq28 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq50 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq46
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq50 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq50
    | exact resolve eq50 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq50
  have eq60 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X1
       have i₂ := eq9 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq9 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq118 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq114 X0 X1
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq114
    | (have j0 := eq114 X0 X1
       grind)
    | exact resolve eq114 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq148 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 (σ X0) X1 X2
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq61
    | exact resolve eq61 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) (M.op X0 (M.op X1 X1)) X2
       have i₂ := eq61 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X0 X1
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq184 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq10
    | exact resolve eq10 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1637 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op (M.op (M.op X2 X2) (M.op X3 X3)) X0)) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq60 X0 X2 X3 X1
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq60 X1 X1 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq60
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1692 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1637 X0 X1 x x
       have i₂ := eq60 X0 x x X0
       grind)
    | exact superpose eq60 eq1637
    | (have j0 := eq1637 X0 X1 x x
       grind)
    | exact resolve eq1637 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq1637
  have eq1693 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1692 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1692
  have eq4084 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq118 x y
       grind)
    | exact superpose eq118 eq16
    | (have j1 := eq118 x y
       grind)
    | exact resolve eq16 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq6003 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X0 (M.op X1 X1))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 X3 (M.op X0 (M.op X1 X1)) x
       have i₂ := eq163 X0 X1 x
       grind)
    | exact superpose eq163 eq9
    | exact resolve eq9 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq13885 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6003 X1 (τ X0) X2
       have i₂ := eq184 X0
       grind)
    | exact superpose eq184 eq6003
    | exact resolve eq6003 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6003
  have eq54529 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X1 X1)) (M.op X2 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq148 X1 X2 (τ X0)
       have i₂ := eq184 X0
       grind)
    | exact superpose eq184 eq148
    | exact resolve eq148 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq184
  have eq59141 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4084
       have i₂ := eq1693 x y
       grind)
    | exact superpose eq1693 eq4084
    | (have j1 := eq1693 (M.op (σ x) (σ y)) (σ (M.op x x))
       grind)
    | (have r₁ := eq4084
       have r₂ := eq1693 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq4084
       have r₂ := eq1693 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq4084 eq1693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1693 eq4084
  have eq59145 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq59141
  have eq812551 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x x)) (M.op (σ x) (τ (M.op X0 X0)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13885 X0 (σ x) (σ y)
       have i₂ := eq59145
       grind)
    | exact superpose eq59145 eq13885
    | exact resolve eq13885 eq59145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13885 eq59145
  have eq812570 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq812551 x
       have i₂ := eq54529 x x (σ x)
       grind)
    | exact superpose eq54529 eq812551
    | exact resolve eq812551 eq54529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54529 eq812551
  have eq812571 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq812570
  have eq812601 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq812571
       grind)
    | exact superpose eq812571 eq10
    | exact resolve eq10 eq812571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812571
  have eq812667 : x = y ∨ x = y := by
    first
    | (have i₁ := eq812601
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq812601
    | exact resolve eq812601 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812601
  have eq812668 : x = y := by grind
  clear eq812667
  have eq813437 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq812668
       grind)
    | exact superpose eq812668 eq16
    | exact resolve eq16 eq812668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812668
  have eq813438 : False := by grind
  exact eq813438

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyx_pyy_pyx_pyy_pyx_Equation3058 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X1) X0) = X0 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X0 := by
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
  have eq26 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq51 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq51 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq51 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq52 (σ X0)
       grind)
    | exact superpose eq52 eq15
    | exact resolve eq15 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq54 X0
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq54
    | exact resolve eq54 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq73 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (k X1 (τ X0))
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq63
    | exact resolve eq63 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq88 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq81
    | (have j0 := eq81 X0 X1
       grind)
    | exact resolve eq81 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq90 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq63 X1
       grind)
    | exact superpose eq63 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq88
  have eq128 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq90 (k X1 (τ X0)) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq90
    | (have j0 := eq90 X0 X2
       grind)
    | exact resolve eq90 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq148 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq128 X0 X1 X2
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq128
    | (have j0 := eq128 X0 X1 X2
       grind)
    | exact resolve eq128 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq128
  have eq1135 : ∀ X0 X1 X2 X3 : G, (M.op (k (σ X0) X1) (σ X2)) ≠ (M.op (k (σ X0) X1) X3) ∨ (M.op (k (σ X0) X1) (σ X2)) = (k X3 (k (σ X0) X1)) ∨ (M.op X3 X3) = X3 ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 (k (σ X0) X1)
       have i₂ := eq148 X0 X1 X2
       grind)
    | exact superpose eq148 eq13
    | (have j0 := eq13 X3 X1
       have j1 := eq148 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X2) (k (σ X0) X1)
       have r₂ := eq148 X0 X1 X2
       grind)
    | exact resolve eq13 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq50199 : ∀ X0 X1 X2 : G, (k (σ X2) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1135 X0 X1 X2 (σ X2)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq50202 : ∀ X0 X1 X2 : G, (k (σ X2) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq50199 X0 X1 X2
       have j1 := eq12 (σ X2) (k (σ X0) X1)
       grind)
    | (have r₁ := eq50199 X0 X1 X2
       have r₂ := eq12 (σ X2) X1
       grind)
    | exact resolve eq50199 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50199
  have eq50266 : ∀ X0 X1 X2 : G, (k (σ X2) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq50202 X0 X1 X2
       have j1 := eq75 X2 (k (σ X0) X1)
       grind)
    | (have r₁ := eq50202 X0 X1 X0
       have r₂ := eq75 X0 X1
       grind)
    | exact resolve eq50202 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq50202
  have eq50317 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50266 X0 X1 X2
       have i₂ := eq26 X0 X1 X2
       grind)
    | exact superpose eq26 eq50266
    | (have j0 := eq50266 X0 X1 X2
       grind)
    | exact resolve eq50266 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq50266
  have eq50318 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq50317 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50317
  have eq50537 : ∀ X0 X1 X2 : G, (k X2 (σ (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X2 (k X0 (τ X1))
       have i₂ := eq50318 X0 X1 (τ X2)
       grind)
    | exact superpose eq50318 eq17
    | exact resolve eq17 eq50318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq50318
  have eq50710 : ∀ X0 X1 X2 : G, (k X2 (σ (k X0 (τ X1)))) = (M.op (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50537 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq50537
    | exact resolve eq50537 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50537
  have eq50858 : ∀ X0 X1 X2 : G, (k X2 (k (σ X0) X1)) = (M.op (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50710 X0 X1 X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq50710
    | exact resolve eq50710 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq50710
  have eq50991 : ∀ X0 X1 X2 : G, (k X1 (k X0 X2)) = (M.op (k X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50858 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq50858
    | exact resolve eq50858 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50858
  have eq51978 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq50991 X0 X1 X0
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq50991
    | exact resolve eq50991 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq51995 : ∀ X0 X1 X2 X3 : G, (k X3 (M.op (k X0 X1) X2)) = (M.op (M.op (k X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq50991 X1 X1 (k X0 X2)
       have i₂ := eq50991 X0 X1 X2
       grind)
    | exact superpose eq50991 eq50991
    | exact resolve eq50991 eq50991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50991
  have eq75592 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X3) X2) = (k X2 (M.op (M.op (M.op X0 X0) X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51995 X1 (M.op X0 X0) X2 X3
       have i₂ := eq51978 X0 X1
       grind)
    | exact superpose eq51978 eq51995
    | exact resolve eq51995 eq51978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51978 eq51995
  have eq291983 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq75592 (M.op X0 X0) (M.op X0 X0) x X0
       have i₂ := eq9 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq75592
    | exact resolve eq75592 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75592
  have eq293196 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq291983 (σ X0) (σ X1)
       grind)
    | exact superpose eq291983 eq15
    | exact resolve eq15 eq291983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293554 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq293196 X0 X1
       have i₂ := eq291983 X0 X1
       grind)
    | exact superpose eq291983 eq293196
    | exact resolve eq293196 eq291983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291983 eq293196
  have eq335601 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq293554 x y
       grind)
    | exact superpose eq293554 eq16
    | (have r₁ := eq16
       have r₂ := eq293554 x y
       grind)
    | exact resolve eq16 eq293554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293554
  have eq335830 : False := by grind
  exact eq335830

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pxy_pxy_pxx_pxy_Equation3058 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq15
    | exact resolve eq15 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq32 (τ X0)
       grind)
    | exact superpose eq32 eq18
    | exact resolve eq18 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq36
    | exact resolve eq36 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
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
  clear eq34
  have eq41 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq37
    | exact resolve eq37 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq37
  have eq43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq75 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq89 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq82
    | (have j0 := eq82 X0 X1
       grind)
    | exact resolve eq82 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 X1
       have i₂ := eq39 X1
       grind)
    | exact superpose eq39 eq89
    | (have j0 := eq89 X0 X1
       grind)
    | exact resolve eq89 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq158 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq91
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq192 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq158 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq158
    | (have j0 := eq158 X0 X1
       grind)
    | exact resolve eq158 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq158
  have eq196 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq192 X0 X1
       have j1 := eq76 X1 X0
       grind)
    | (have r₁ := eq192 X1 (τ X1)
       have r₂ := eq76 (τ X1) X1
       grind)
    | (have r₁ := eq192 X1 X0
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq192 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq200 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq196 X0 X1
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq196
    | (have j0 := eq196 X0 X1
       grind)
    | exact resolve eq196 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq357 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq200 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq200
    | exact resolve eq200 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq367 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq200 (σ X0) X1
       grind)
    | exact superpose eq200 eq15
    | (have j1 := eq200 (σ X0) X1
       grind)
    | exact resolve eq15 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq378 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq367 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq367
    | (have j0 := eq367 X0 X1
       grind)
    | exact resolve eq367 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq392 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq357 (τ X1) X0
       grind)
    | exact superpose eq357 eq18
    | (have j1 := eq357 (τ X1) X0
       grind)
    | exact resolve eq18 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1064 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq392 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq392
    | exact resolve eq392 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq1118 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1064 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1064
    | (have j0 := eq1064 X0 X1
       grind)
    | exact resolve eq1064 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq3940 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq378 x y
       grind)
    | exact superpose eq378 eq16
    | (have j1 := eq378 x y
       grind)
    | exact resolve eq16 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3965 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq378 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq4127 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3940
       have i₂ := eq1118 y x
       grind)
    | exact superpose eq1118 eq3940
    | (have j1 := eq1118 y x
       grind)
    | (have r₁ := eq3940
       have r₂ := eq1118 y x
       grind)
    | exact resolve eq3940 eq1118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118 eq3940
  have eq4128 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq4127
  have eq4131 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq4128
       grind)
    | exact superpose eq4128 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq4128
       grind)
    | exact resolve eq13 eq4128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4132 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) ∨ (k x y) = (M.op x x) := by grind
  clear eq4131
  have eq4165 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3965 (τ X0) (τ X1)
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq3965
    | (have j0 := eq3965 (τ X0) (τ X1)
       grind)
    | exact resolve eq3965 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq4217 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4165 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq4165
    | (have j0 := eq4165 X0 X1
       grind)
    | exact resolve eq4165 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4165
  have eq4238 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4217 X0 X1
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq4217
    | (have j0 := eq4217 X0 X1
       grind)
    | exact resolve eq4217 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4217
  have eq4254 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4238 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq4238
    | (have j0 := eq4238 X0 X1
       grind)
    | exact resolve eq4238 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4238
  have eq4264 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4254 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4254
    | (have j0 := eq4254 X0 X1
       grind)
    | exact resolve eq4254 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4254
  have eq4269 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4264 X0 X1
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq4264
    | (have j0 := eq4264 X0 X1
       grind)
    | exact resolve eq4264 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq4264
  have eq53132 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq75 x (σ y)
       have i₂ := eq4132
       grind)
    | exact superpose eq4132 eq75
    | (have j0 := eq75 x (σ y)
       grind)
    | (have r₁ := eq75 x (σ y)
       have r₂ := eq4132
       grind)
    | exact resolve eq75 eq4132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq53133 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq76 y (σ x)
       have i₂ := eq4132
       grind)
    | exact superpose eq4132 eq76
    | exact resolve eq76 eq4132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4132
  have eq53157 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (k x y) = (M.op x x) := by grind
  clear eq53132
  have eq53159 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq53133
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq53133
    | exact resolve eq53133 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53133
  have eq53160 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq53157
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq53157
    | exact resolve eq53157 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53157
  have eq53162 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq53160
       have i₂ := eq39 y
       grind)
    | exact superpose eq39 eq53160
    | exact resolve eq53160 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq53160
  have eq53164 : (k x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq53162
       have r₂ := eq53159
       grind)
    | exact resolve eq53162 eq53159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53159 eq53162
  have eq53946 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq53164
       have i₂ := eq357 y x
       grind)
    | exact superpose eq357 eq53164
    | (have j1 := eq357 y x
       grind)
    | exact resolve eq53164 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq53972 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3965 x y
       have i₂ := eq53164
       grind)
    | exact superpose eq53164 eq3965
    | (have j0 := eq3965 x y
       grind)
    | (have r₁ := eq3965 x y
       have r₂ := eq53164
       grind)
    | exact resolve eq3965 eq53164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53164
  have eq54017 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq53972
  have eq54024 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq53946
  have eq54025 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have j1 := eq3965 x y
       grind)
    | (have r₁ := eq54017
       have r₂ := eq3965 x y
       grind)
    | exact resolve eq54017 eq3965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54017
  have eq54032 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq54025
       grind)
    | exact superpose eq54025 eq16
    | exact resolve eq16 eq54025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54025
  have eq55385 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq54032
       have i₂ := eq54024
       grind)
    | exact superpose eq54024 eq54032
    | (have r₁ := eq54032
       have r₂ := eq54024
       grind)
    | exact resolve eq54032 eq54024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54024
  have eq55392 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq55385
  have eq55393 : (M.op x x) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq55392
  have eq55396 : (M.op x x) = (M.op y y) := by
    first
    | (have r₁ := eq55393
       have r₂ := eq54032
       grind)
    | exact resolve eq55393 eq54032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54032 eq55393
  have eq55398 : ∀ X0 : G, (M.op x x) ≠ (M.op X0 y) ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq55396
       grind)
    | exact superpose eq55396 eq12
    | (have j0 := eq12 X0 y
       grind)
    | exact resolve eq12 eq55396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56295 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq55398 x
       have i₂ := eq4128
       grind)
    | exact superpose eq4128 eq55398
    | (have r₁ := eq55398 x
       have r₂ := eq4128
       grind)
    | exact resolve eq55398 eq4128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4128 eq55398
  have eq56300 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by grind
  clear eq56295
  have eq58128 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq76 y (σ x)
       have i₂ := eq56300
       grind)
    | exact superpose eq56300 eq76
    | exact resolve eq76 eq56300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56300
  have eq58154 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq58128
       have i₂ := eq55396
       grind)
    | exact superpose eq55396 eq58128
    | exact resolve eq58128 eq55396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58128
  have eq58155 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by grind
  clear eq58154
  have eq58158 : (k x y) = (M.op x x) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq58155
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq58155
    | exact resolve eq58155 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58155
  have eq58524 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3965 x y
       have i₂ := eq58158
       grind)
    | exact superpose eq58158 eq3965
    | (have j0 := eq3965 x y
       grind)
    | (have r₁ := eq3965 x y
       have r₂ := eq58158
       grind)
    | exact resolve eq3965 eq58158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58158
  have eq58569 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq58524
  have eq58577 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have j1 := eq3965 x y
       grind)
    | (have r₁ := eq58569
       have r₂ := eq3965 x y
       grind)
    | exact resolve eq58569 eq3965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3965 eq58569
  have eq58586 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq58577
       grind)
    | exact superpose eq58577 eq16
    | exact resolve eq16 eq58577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58588 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq76 y (σ x)
       have i₂ := eq58577
       grind)
    | exact superpose eq58577 eq76
    | exact resolve eq76 eq58577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq58577
  have eq58614 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq58588
       have i₂ := eq55396
       grind)
    | exact superpose eq55396 eq58588
    | exact resolve eq58588 eq55396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55396 eq58588
  have eq58615 : (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq58614
  have eq58618 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq58615
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq58615
    | exact resolve eq58615 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58615
  have eq58970 : (k x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq58618
       grind)
    | exact superpose eq58618 eq10
    | exact resolve eq10 eq58618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58618
  have eq59128 : (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq58970
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq58970
    | exact resolve eq58970 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58970
  have eq59860 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq4269 x y
       have i₂ := eq59128
       grind)
    | exact superpose eq59128 eq4269
    | (have j0 := eq4269 x y
       grind)
    | (have r₁ := eq4269 x y
       have r₂ := eq59128
       grind)
    | exact resolve eq4269 eq59128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4269 eq59128
  have eq59901 : (M.op x y) = (M.op x x) := by grind
  clear eq59860
  have eq59914 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq58586
       have i₂ := eq59901
       grind)
    | exact superpose eq59901 eq58586
    | exact resolve eq58586 eq59901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58586 eq59901
  have eq59919 : False := by grind
  exact eq59919

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_pyx_pyx_pxy_pyx_Equation3058 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq456 : ∀ X0 X1 : G, (M.op (τ X1) X0) = X0 ∨ (M.op X0 (τ X1)) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3480 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (τ X1) X0) = (M.op X0 (τ X1)) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X1) X0
       have i₂ := eq456 X0 X1
       grind)
    | exact superpose eq456 eq12
    | (have j0 := eq12 (τ X1) X0
       have j1 := eq456 X0 X1
       grind)
    | (have r₁ := eq12 (τ X1) X0
       have r₂ := eq456 X0 X1
       grind)
    | exact resolve eq12 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq3482 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op X0 (τ X1)) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3480 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3480
  have eq14289 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq3482 X0 X1
       grind)
    | exact superpose eq3482 eq17
    | (have j1 := eq3482 X0 X1
       grind)
    | exact resolve eq17 eq3482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq3482
  have eq14375 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq14289 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14289
  have eq14419 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14375 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14375
    | exact resolve eq14375 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14375
  have eq14589 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14419 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14419
    | (have j0 := eq14419 X0 X1
       grind)
    | exact resolve eq14419 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14419
  have eq14675 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq14589 X1 X0
       grind)
    | exact superpose eq14589 eq10
    | (have j1 := eq14589 X0 X1
       grind)
    | exact resolve eq10 eq14589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14837 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14675 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq14675
    | (have j0 := eq14675 X0 X1
       grind)
    | exact resolve eq14675 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14675
  have eq14976 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14837 (σ X0) (σ X1)
       grind)
    | exact superpose eq14837 eq15
    | (have j1 := eq14837 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14837
  have eq19990 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14976 x y
       grind)
    | exact superpose eq14976 eq16
    | (have j1 := eq14976 y x
       grind)
    | exact resolve eq16 eq14976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14976
  have eq20069 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq19990
       have i₂ := eq14589 y x
       grind)
    | exact superpose eq14589 eq19990
    | (have j1 := eq14589 (σ x) (σ y)
       grind)
    | (have r₁ := eq19990
       have r₂ := eq14589 y x
       grind)
    | exact resolve eq19990 eq14589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20072 : (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq20069
  have eq20085 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq20072
       grind)
    | exact superpose eq20072 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq20072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20086 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq20072
       grind)
    | exact superpose eq20072 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq20072
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq20072
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq20072
       grind)
    | exact resolve eq13 eq20072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20072
  have eq20089 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq20086
  have eq20090 : (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq20085
       have r₂ := eq20089
       grind)
    | exact resolve eq20085 eq20089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20085 eq20089
  have eq20091 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq19990
       have i₂ := eq20090
       grind)
    | exact superpose eq20090 eq19990
    | exact resolve eq19990 eq20090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19990 eq20090
  have eq20095 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq20091
  have eq20096 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq20095
  have eq20110 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq20096
       grind)
    | exact superpose eq20096 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq20096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20111 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq20096
       grind)
    | exact superpose eq20096 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq20096
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq20096
       grind)
    | exact resolve eq13 eq20096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20096
  have eq20114 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq20111
  have eq20116 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20114
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq20114
    | exact resolve eq20114 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20114
  have eq20117 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20110
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq20110
    | exact resolve eq20110 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20110
  have eq20120 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq20117
       have r₂ := eq20116
       grind)
    | exact resolve eq20117 eq20116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20116 eq20117
  have eq20132 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20120
       grind)
    | exact superpose eq20120 eq16
    | exact resolve eq16 eq20120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20120
  have eq20232 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq20132
       have i₂ := eq14589 y x
       grind)
    | exact superpose eq14589 eq20132
    | (have j1 := eq14589 x y
       grind)
    | (have r₁ := eq20132
       have r₂ := eq14589 y x
       grind)
    | exact resolve eq20132 eq14589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14589
  have eq20235 : (M.op x y) = (M.op y x) := by grind
  clear eq20232
  have eq20249 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq20235
       grind)
    | exact superpose eq20235 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq20235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20250 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq20235
       grind)
    | exact superpose eq20235 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq20235
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq20235
       grind)
    | exact resolve eq13 eq20235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20235
  have eq20253 : x = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq20250
  have eq20254 : (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq20249
       have r₂ := eq20253
       grind)
    | exact resolve eq20249 eq20253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20249 eq20253
  have eq20255 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq20132
       have i₂ := eq20254
       grind)
    | exact superpose eq20254 eq20132
    | exact resolve eq20132 eq20254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20132 eq20254
  have eq20260 : False := by grind
  exact eq20260

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pyx_pxx_pyx_Equation3058 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X1) X0) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq69 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq138 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq481 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq69 X0 X0
       grind)
    | exact superpose eq69 eq9
    | (have j1 := eq69 X0 x
       grind)
    | exact resolve eq9 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq488 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq481 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq481 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq481 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq505 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq488 (σ X0)
       grind)
    | exact superpose eq488 eq15
    | exact resolve eq15 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq524 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq505 X0
       have i₂ := eq488 X0
       grind)
    | exact superpose eq488 eq505
    | exact resolve eq505 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488 eq505
  have eq769 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq138 x y
       grind)
    | exact superpose eq138 eq16
    | (have j1 := eq138 x y
       grind)
    | exact resolve eq16 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq775 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq138 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq2818 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq145 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq145
    | exact resolve eq145 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq2877 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2818 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2818
    | (have j0 := eq2818 X0 X1
       grind)
    | exact resolve eq2818 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2818
  have eq3026 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq775 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq775
    | (have j0 := eq775 (τ X0) (τ X1)
       grind)
    | exact resolve eq775 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq3074 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3026 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq3026
    | (have j0 := eq3026 X0 X1
       grind)
    | exact resolve eq3026 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3026
  have eq3095 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3074 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3074
    | (have j0 := eq3074 X0 X1
       grind)
    | exact resolve eq3074 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3074
  have eq3109 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3095 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3095
    | (have j0 := eq3095 X0 X1
       grind)
    | exact resolve eq3095 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3095
  have eq3113 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3109 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3109
    | (have j0 := eq3109 X0 X1
       grind)
    | exact resolve eq3109 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3109
  have eq3116 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ X0 = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3113 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3113
    | (have j0 := eq3113 X0 X1
       grind)
    | exact resolve eq3113 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3113
  have eq3118 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3116 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3116
    | (have j0 := eq3116 X0 X1
       grind)
    | exact resolve eq3116 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3116
  have eq15960 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq769
       have i₂ := eq2877 x y
       grind)
    | exact superpose eq2877 eq769
    | (have j1 := eq2877 (σ x) (σ y)
       grind)
    | (have r₁ := eq769
       have r₂ := eq2877 x y
       grind)
    | (have r₁ := eq769
       have r₂ := eq2877 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq769
       have r₂ := eq2877 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq769 eq2877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769 eq2877
  have eq15961 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq15960
  have eq15963 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15961
       grind)
    | exact superpose eq15961 eq16
    | exact resolve eq16 eq15961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15961
  have eq15964 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq15963
       have r₂ := eq524 x
       grind)
    | exact resolve eq15963 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15963
  have eq15967 : y ≠ y ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq15964
       grind)
    | exact superpose eq15964 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq15964
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq15964
       grind)
    | exact resolve eq12 eq15964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15964
  have eq15968 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k y x) := by grind
  clear eq15967
  have eq15973 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq15968
       grind)
    | exact superpose eq15968 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq15968
       grind)
    | exact resolve eq12 eq15968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15968
  have eq15974 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k y x) := by grind
  clear eq15973
  have eq15976 : y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq15974
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq15974
    | exact resolve eq15974 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15974
  have eq15988 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq775 x y
       have i₂ := eq15976
       grind)
    | exact superpose eq15976 eq775
    | (have j0 := eq775 x y
       grind)
    | (have r₁ := eq775 x y
       have r₂ := eq15976
       grind)
    | exact resolve eq775 eq15976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15976
  have eq16007 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq15988
  have eq16008 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq16007
  have eq16012 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq775 x y
       grind)
    | (have r₁ := eq16008
       have r₂ := eq775 x y
       grind)
    | exact resolve eq16008 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775 eq16008
  have eq16015 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16012
       grind)
    | exact superpose eq16012 eq16
    | exact resolve eq16 eq16012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16018 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq16012
       grind)
    | exact superpose eq16012 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq16012
       grind)
    | exact resolve eq12 eq16012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16012
  have eq16019 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq16018
  have eq16021 : (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16019
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq16019
    | exact resolve eq16019 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16019
  have eq16031 : y = (τ (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq16021
       grind)
    | exact superpose eq16021 eq10
    | exact resolve eq10 eq16021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16021
  have eq16103 : x = y ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16031
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq16031
    | exact resolve eq16031 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16031
  have eq16111 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16103
       grind)
    | exact superpose eq16103 eq16
    | exact resolve eq16 eq16103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16103
  have eq16112 : (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq16111
       have r₂ := eq524 x
       grind)
    | exact resolve eq16111 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16111
  have eq16122 : (k y x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq16112
       grind)
    | exact superpose eq16112 eq10
    | exact resolve eq10 eq16112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16112
  have eq16195 : y = (k y x) := by
    first
    | (have i₁ := eq16122
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq16122
    | exact resolve eq16122 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16122
  have eq16214 : y ≠ y ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3118 y x
       have i₂ := eq16195
       grind)
    | exact superpose eq16195 eq3118
    | (have j0 := eq3118 x y
       grind)
    | (have r₁ := eq3118 y x
       have r₂ := eq16195
       grind)
    | exact resolve eq3118 eq16195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3118 eq16195
  have eq16226 : y = (M.op x y) ∨ x = y := by grind
  clear eq16214
  have eq16230 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16015
       have i₂ := eq16226
       grind)
    | exact superpose eq16226 eq16015
    | exact resolve eq16015 eq16226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16015 eq16226
  have eq16237 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq16230
  have eq16238 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16237
       grind)
    | exact superpose eq16237 eq16
    | exact resolve eq16 eq16237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16237
  have eq16243 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq16238
       have r₂ := eq524 x
       grind)
    | exact resolve eq16238 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16238
  have eq16244 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16243
       grind)
    | exact superpose eq16243 eq16
    | exact resolve eq16 eq16243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16245 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq16243
       grind)
    | exact superpose eq16243 eq10
    | exact resolve eq10 eq16243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16243
  have eq16317 : x = y := by
    first
    | (have i₁ := eq16245
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq16245
    | exact resolve eq16245 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16245
  have eq16318 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16244
       have i₂ := eq524 x
       grind)
    | exact superpose eq524 eq16244
    | exact resolve eq16244 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524 eq16244
  have eq16323 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16318
       have i₂ := eq16317
       grind)
    | exact superpose eq16317 eq16318
    | exact resolve eq16318 eq16317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16317 eq16318
  have eq16324 : False := by grind
  exact eq16324

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxy_pyx_pxy_Equation3058 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq83 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq135 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq83 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq83 X0 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq139 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq135 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq140 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq139 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq145 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq140 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq140
    | (have j0 := eq140 X0 X1
       grind)
    | exact resolve eq140 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq146 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq145 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq512 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq146 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq146
    | exact resolve eq146 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq146 x y
       grind)
    | exact superpose eq146 eq16
    | (have j1 := eq146 x y
       grind)
    | exact resolve eq16 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq534 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq512 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq512
    | (have j0 := eq512 X0 X1
       grind)
    | exact resolve eq512 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq512
  have eq536 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq534 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq534
    | exact resolve eq534 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq595 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq536 (τ X0) X1
       grind)
    | exact superpose eq536 eq18
    | (have j1 := eq536 (τ X0) X1
       grind)
    | exact resolve eq18 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq536
  have eq836 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq595 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq595
    | exact resolve eq595 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq889 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq836 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq836
    | (have j0 := eq836 X0 X1
       grind)
    | exact resolve eq836 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq1005 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq520
       have i₂ := eq889 x y
       grind)
    | exact superpose eq889 eq520
    | (have j1 := eq889 (σ x) (σ y)
       grind)
    | (have r₁ := eq520
       have r₂ := eq889 x y
       grind)
    | exact resolve eq520 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1006 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1005
  have eq1011 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1006
  have eq1070 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq520
       have i₂ := eq1011
       grind)
    | exact superpose eq1011 eq520
    | exact resolve eq520 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520 eq1011
  have eq1071 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1070
  have eq1072 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1071
  have eq1083 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1072
  have eq1093 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1083
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1083
    | exact resolve eq1083 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq1153 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1093
       grind)
    | exact superpose eq1093 eq16
    | exact resolve eq16 eq1093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq1159 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1153
       have i₂ := eq889 x y
       grind)
    | exact superpose eq889 eq1153
    | (have j1 := eq889 x y
       grind)
    | (have r₁ := eq1153
       have r₂ := eq889 x y
       grind)
    | exact resolve eq1153 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889
  have eq1160 : x = (M.op y y) := by grind
  clear eq1159
  have eq1207 : (M.op x y) = (k x y) := by grind
  clear eq1160
  have eq1213 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1153
       have i₂ := eq1207
       grind)
    | exact superpose eq1207 eq1153
    | exact resolve eq1153 eq1207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153 eq1207
  have eq1216 : False := by grind
  exact eq1216

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pxx_pxy_Equation3058 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X1) X0) = X0 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq27 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq51 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq51 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq51 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq52 (σ X0)
       grind)
    | exact superpose eq52 eq15
    | exact resolve eq15 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq54 X0
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq54
    | exact resolve eq54 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq73 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (k X1 (τ X0))
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq63
    | exact resolve eq63 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq88 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq81
    | (have j0 := eq81 X0 X1
       grind)
    | exact resolve eq81 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq63 X1
       grind)
    | exact superpose eq63 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq88
  have eq128 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq90 (k X1 (τ X0)) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq90
    | (have j0 := eq90 X0 X2
       grind)
    | exact resolve eq90 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq148 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq128 X0 X1 X2
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq128
    | (have j0 := eq128 X0 X1 X2
       grind)
    | exact resolve eq128 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq128
  have eq1135 : ∀ X0 X1 X2 X3 : G, (M.op (k (σ X0) X1) (σ X2)) ≠ (M.op (k (σ X0) X1) X3) ∨ (M.op (k (σ X0) X1) (σ X2)) = (k (k (σ X0) X1) X3) ∨ (M.op X3 X3) = X3 ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (k (σ X0) X1) X1
       have i₂ := eq148 X0 X1 X2
       grind)
    | exact superpose eq148 eq13
    | (have j0 := eq13 X0 X3
       have j1 := eq148 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (σ X2)
       have r₂ := eq148 X0 X1 X2
       grind)
    | exact resolve eq13 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq50234 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1135 X0 X1 X2 (σ X2)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq50237 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq50234 X0 X1 X2
       have j1 := eq12 (k (σ X0) X1) (σ X2)
       grind)
    | (have r₁ := eq50234 X0 X1 X2
       have r₂ := eq12 X0 (σ X2)
       grind)
    | exact resolve eq50234 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50234
  have eq50304 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq50237 X0 X1 X2
       have j1 := eq75 X2 (k (σ X0) X1)
       grind)
    | (have r₁ := eq50237 X0 X1 X0
       have r₂ := eq75 X0 X1
       grind)
    | exact resolve eq50237 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq50237
  have eq50357 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50304 X0 X1 X2
       have i₂ := eq27 X0 X1 X2
       grind)
    | exact superpose eq27 eq50304
    | (have j0 := eq50304 X0 X1 X2
       grind)
    | exact resolve eq50304 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq50304
  have eq50358 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq50357 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50357
  have eq50577 : ∀ X0 X1 X2 : G, (k (σ (k X0 (τ X1))) X2) = (M.op (k (σ X0) X1) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X2 (k X0 (τ X1))
       have i₂ := eq50358 X0 X1 (τ X2)
       grind)
    | exact superpose eq50358 eq18
    | exact resolve eq18 eq50358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50358
  have eq50742 : ∀ X0 X1 X2 : G, (k (σ (k X0 (τ X1))) X2) = (M.op (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50577 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq50577
    | exact resolve eq50577 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50577
  have eq50878 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) X2) = (M.op (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50742 X0 X1 X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq50742
    | exact resolve eq50742 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq50742
  have eq51008 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (M.op (k X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50878 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq50878
    | exact resolve eq50878 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50878
  have eq51961 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51008 X0 X0 x
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq51008
    | exact resolve eq51008 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq52024 : ∀ X0 X1 X2 X3 : G, (k (M.op (k X0 X1) X2) X3) = (M.op (M.op (k X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51008 (k X0 X1) X2 X2
       have i₂ := eq51008 X0 X1 X2
       grind)
    | exact superpose eq51008 eq51008
    | exact resolve eq51008 eq51008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51008
  have eq74828 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X2) X3) = (k (M.op (M.op (M.op X0 X0) X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52024 (M.op X0 X0) X1 X2 X3
       have i₂ := eq51961 X0 X1
       grind)
    | exact superpose eq51961 eq52024
    | exact resolve eq52024 eq51961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51961 eq52024
  have eq276385 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq74828 (M.op X0 X0) (M.op X0 X0) X0 x
       have i₂ := eq9 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq74828
    | exact resolve eq74828 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74828
  have eq280377 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq276385 (σ X0) (σ X1)
       grind)
    | exact superpose eq276385 eq15
    | exact resolve eq15 eq276385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280696 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq280377 X0 X1
       have i₂ := eq276385 X0 X1
       grind)
    | exact superpose eq276385 eq280377
    | exact resolve eq280377 eq276385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276385 eq280377
  have eq314165 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq280696 x y
       grind)
    | exact superpose eq280696 eq16
    | (have r₁ := eq16
       have r₂ := eq280696 x y
       grind)
    | exact resolve eq16 eq280696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280696
  have eq314393 : False := by grind
  exact eq314393

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation3058 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3058 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq452 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq453 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
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
  clear eq19
  have eq456 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq479 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq456 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq456
    | (have j0 := eq456 X0 X1
       grind)
    | exact resolve eq456 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq822 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq479 x y
       grind)
    | exact superpose eq479 eq16
    | (have j1 := eq479 x y
       grind)
    | exact resolve eq16 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq3165 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq453 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq453
    | exact resolve eq453 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq3210 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3165 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3165
    | (have j0 := eq3165 X0 X1
       grind)
    | exact resolve eq3165 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3165
  have eq3472 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (σ X1) = X0 ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq452 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq452 X0 X1
       grind)
    | exact superpose eq452 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq452 X1 X0
       grind)
    | (have r₁ := eq13 X1 (σ X0)
       have r₂ := eq452 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq452 X0 (σ X0)
       grind)
    | exact resolve eq13 eq452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq3475 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (σ X1) = X0 ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3472 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3472
  have eq3476 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op (σ X1) X0)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3475 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3475
  have eq3715 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3476 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3476
    | exact resolve eq3476 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3476
  have eq3806 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3715 X0 X1
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq3715
    | (have j0 := eq3715 X0 X1
       grind)
    | exact resolve eq3715 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq3715
  have eq3834 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq3806 X0 X1
       grind)
    | exact superpose eq3806 eq11
    | (have j1 := eq3806 X0 X1
       grind)
    | exact resolve eq11 eq3806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3806
  have eq3953 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3834 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq3834
    | (have j0 := eq3834 X0 X1
       grind)
    | exact resolve eq3834 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3834
  have eq3973 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3953 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3953
    | (have j0 := eq3953 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq3953 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3953
  have eq4131 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3973 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq3973
    | (have j0 := eq3973 X0 X1
       grind)
    | exact resolve eq3973 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3973
  have eq8775 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq822
       have i₂ := eq3210 x y
       grind)
    | exact superpose eq3210 eq822
    | (have j1 := eq3210 x y
       grind)
    | (have r₁ := eq822
       have r₂ := eq3210 x y
       grind)
    | (have r₁ := eq822
       have r₂ := eq3210 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq822
       have r₂ := eq3210 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq822 eq3210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8776 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq8775
  have eq12107 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4131 y x
       grind)
    | exact superpose eq4131 eq16
    | (have j1 := eq4131 y x
       grind)
    | exact resolve eq16 eq4131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4131
  have eq12183 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq12107
       have i₂ := eq3210 x y
       grind)
    | exact superpose eq3210 eq12107
    | (have j1 := eq3210 x y
       grind)
    | (have r₁ := eq12107
       have r₂ := eq3210 x y
       grind)
    | (have r₁ := eq12107
       have r₂ := eq3210 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq12107
       have r₂ := eq3210 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq12107 eq3210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3210
  have eq12184 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq12183
  have eq12312 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12184
       grind)
    | exact superpose eq12184 eq16
    | exact resolve eq16 eq12184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12184
  have eq12313 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq12312
       have r₂ := eq22 x
       grind)
    | exact resolve eq12312 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12312
  have eq23352 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq8776
       grind)
    | exact superpose eq8776 eq16
    | exact resolve eq16 eq8776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8776
  have eq23371 : x = y ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq23352
       have r₂ := eq12313
       grind)
    | exact resolve eq23352 eq12313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12313 eq23352
  have eq23379 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23371
       grind)
    | exact superpose eq23371 eq16
    | exact resolve eq16 eq23371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23371
  have eq23383 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq23379
       have r₂ := eq22 x
       grind)
    | exact resolve eq23379 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23379
  have eq23386 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = X0 ∨ (M.op x y) = (k y X0) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq13 y x
       have i₂ := eq23383
       grind)
    | exact superpose eq23383 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq23383
       grind)
    | exact resolve eq13 eq23383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23383
  have eq23465 : x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have j0 := eq23386 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23386
  have eq23471 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23465
       grind)
    | exact superpose eq23465 eq16
    | exact resolve eq16 eq23465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23465
  have eq23475 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq23471
       have r₂ := eq22 x
       grind)
    | exact resolve eq23471 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23471
  have eq23481 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq822
       have i₂ := eq23475
       grind)
    | exact superpose eq23475 eq822
    | exact resolve eq822 eq23475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq23482 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12107
       have i₂ := eq23475
       grind)
    | exact superpose eq23475 eq12107
    | exact resolve eq12107 eq23475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12107 eq23475
  have eq23497 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by grind
  clear eq23482
  have eq23498 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq23497
  have eq23499 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by grind
  clear eq23481
  have eq23500 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by grind
  clear eq23499
  have eq23505 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq23498
       grind)
    | exact superpose eq23498 eq10
    | exact resolve eq10 eq23498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23498
  have eq23678 : x = y ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq23505
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq23505
    | exact resolve eq23505 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23505
  have eq23680 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23678
       grind)
    | exact superpose eq23678 eq16
    | exact resolve eq16 eq23678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23678
  have eq23684 : (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq23680
       have r₂ := eq22 x
       grind)
    | exact resolve eq23680 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23680
  have eq25436 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23500
       grind)
    | exact superpose eq23500 eq16
    | exact resolve eq16 eq23500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23500
  have eq25459 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq25436
       have r₂ := eq23684
       grind)
    | exact resolve eq25436 eq23684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23684 eq25436
  have eq25466 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25459
       grind)
    | exact superpose eq25459 eq16
    | exact resolve eq16 eq25459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25469 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq25459
       grind)
    | exact superpose eq25459 eq10
    | exact resolve eq10 eq25459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25459
  have eq25660 : x = y := by
    first
    | (have i₁ := eq25469
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq25469
    | exact resolve eq25469 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25469
  have eq25661 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq25466
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq25466
    | exact resolve eq25466 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq25466
  have eq25667 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq25661
       have i₂ := eq25660
       grind)
    | exact superpose eq25660 eq25661
    | exact resolve eq25661 eq25660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25660 eq25661
  have eq25668 : False := by grind
  exact eq25668
