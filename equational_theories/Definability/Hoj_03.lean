import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxy_y_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq267 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq267 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq275 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq274 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq380 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq275 (σ x) (σ y)
       grind)
    | exact superpose eq275 eq16
    | (have j1 := eq275 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq382 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq275 X1 X0
       grind)
    | exact superpose eq275 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq275 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq275 X0 X1
       grind)
    | exact resolve eq13 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq390 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq382 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq392 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq390 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq390 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq390 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq393 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq380
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq380
    | exact resolve eq380 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq418 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq392 X1 (τ X0)
       grind)
    | exact superpose eq392 eq17
    | (have j1 := eq392 X1 (τ X0)
       grind)
    | exact resolve eq17 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq424 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq392 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq628 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq418 X1 (τ X0)
       grind)
    | exact superpose eq418 eq18
    | (have j1 := eq418 X1 (τ X0)
       grind)
    | exact resolve eq18 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq418
  have eq633 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq628 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq628
    | (have j0 := eq628 X0 X1
       grind)
    | exact resolve eq628 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq649 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq633 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq633
    | (have j0 := eq633 X0 X1
       grind)
    | exact resolve eq633 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq652 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq649 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq649
    | (have j0 := eq649 X0 X1
       grind)
    | exact resolve eq649 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq726 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq652 X0 X1
       have i₂ := eq392 X0 X1
       grind)
    | exact superpose eq392 eq652
    | (have j0 := eq652 X1 X0
       have j1 := eq392 X1 X0
       grind)
    | exact resolve eq652 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392 eq652
  have eq785 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq726 X0 X1
       have j1 := eq424 X0 X1
       grind)
    | (have r₁ := eq726 X0 X1
       have r₂ := eq424 X0 X1
       grind)
    | exact resolve eq726 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424 eq726
  have eq826 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq785 X1 (σ X0)
       grind)
    | exact superpose eq785 eq22
    | (have j1 := eq785 X1 (σ X0)
       grind)
    | exact resolve eq22 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq785
  have eq859 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq826 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq826
    | (have j0 := eq826 X0 X1
       grind)
    | exact resolve eq826 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq879 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq859 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq859
    | (have j0 := eq859 X0 X1
       grind)
    | exact resolve eq859 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq1474 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq879 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq879
    | exact resolve eq879 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq1549 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1474 x y
       grind)
    | exact superpose eq1474 eq16
    | (have j1 := eq1474 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1474 x y
       grind)
    | exact resolve eq16 eq1474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474
  have eq1570 : y = (k x y) := by grind
  clear eq1549
  have eq2032 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq393
       have i₂ := eq275 x y
       grind)
    | exact superpose eq275 eq393
    | (have j1 := eq275 x y
       grind)
    | exact resolve eq393 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2035 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq2032
  have eq2036 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq2035
       have i₂ := eq1570
       grind)
    | exact superpose eq1570 eq2035
    | exact resolve eq2035 eq1570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2035
  have eq2037 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2036
       have i₂ := eq1570
       grind)
    | exact superpose eq1570 eq2036
    | exact resolve eq2036 eq1570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2036
  have eq2038 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq393
       have i₂ := eq2037
       grind)
    | exact superpose eq2037 eq393
    | exact resolve eq393 eq2037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393 eq2037
  have eq2048 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2038
  have eq2049 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2048
       have i₂ := eq1570
       grind)
    | exact superpose eq1570 eq2048
    | exact resolve eq2048 eq1570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2048
  have eq2050 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2049
  have eq2052 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2050
       grind)
    | exact superpose eq2050 eq16
    | exact resolve eq16 eq2050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2050
  have eq2104 : (σ y) ≠ (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq2052
       have i₂ := eq275 x y
       grind)
    | exact superpose eq275 eq2052
    | (have j1 := eq275 x y
       grind)
    | exact resolve eq2052 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq2107 : (M.op x y) = (k x y) := by grind
  clear eq2104
  have eq2109 : y = (M.op x y) := by
    first
    | (have i₁ := eq2107
       have i₂ := eq1570
       grind)
    | exact superpose eq1570 eq2107
    | exact resolve eq2107 eq1570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1570 eq2107
  have eq2110 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2052
       have i₂ := eq2109
       grind)
    | exact superpose eq2109 eq2052
    | exact resolve eq2052 eq2109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2052 eq2109
  have eq2123 : False := by grind
  exact eq2123

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_pyy_pxy_Equation418 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
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
  have eq110 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq110 (M.op X0 X1)
       grind)
    | exact superpose eq110 eq9
    | exact resolve eq9 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq488 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq496 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq488 X0 X1
       have i₂ := eq110 X1
       grind)
    | exact superpose eq110 eq488
    | (have j0 := eq488 X0 X1
       grind)
    | (have r₁ := eq488 X0 X0
       have r₂ := eq110 X0
       grind)
    | exact resolve eq488 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq520 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq521 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq524 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq551 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq524 X0 X1
       have i₂ := eq110 (σ X0)
       grind)
    | exact superpose eq110 eq524
    | (have j0 := eq524 X0 X1
       grind)
    | exact resolve eq524 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq554 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq521 X0 X1
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq521
    | (have j0 := eq521 X0 X1
       grind)
    | exact resolve eq521 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq555 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq520 X0 X1
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq520
    | (have j0 := eq520 X0 X1
       grind)
    | exact resolve eq520 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq520
  have eq862 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq554 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq554
    | exact resolve eq554 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq887 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq862 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq862
    | (have j0 := eq862 X0 X1
       grind)
    | exact resolve eq862 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq890 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq551 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq551
    | exact resolve eq551 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq922 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq890 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq890
    | (have j0 := eq890 X0 X1
       grind)
    | exact resolve eq890 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq954 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq887 X1 X0
       grind)
    | exact superpose eq887 eq10
    | (have j1 := eq887 X1 X0
       grind)
    | exact resolve eq10 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq992 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq954 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq954
    | (have j0 := eq954 X0 X1
       grind)
    | exact resolve eq954 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq1051 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq922 (σ x) y
       grind)
    | exact superpose eq922 eq16
    | (have j1 := eq922 (σ x) y
       grind)
    | (have r₁ := eq16
       have r₂ := eq922 (M.op (σ x) (σ y)) (M.op x y)
       grind)
    | exact resolve eq16 eq922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq1056 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1051
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1051
    | exact resolve eq1051 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051
  have eq2518 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq555 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq555
    | exact resolve eq555 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq2562 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2518 X0 X1
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq2518
    | (have j0 := eq2518 X0 X1
       grind)
    | exact resolve eq2518 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq2518
  have eq2583 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X1 ∨ X0 = X1 ∨ (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq496 X0 X1
       have i₂ := eq2562 X1 X0
       grind)
    | exact superpose eq2562 eq496
    | (have j0 := eq496 X0 X1
       have j1 := eq2562 X1 X0
       grind)
    | (have r₁ := eq496 X1 X0
       have r₂ := eq2562 X0 X1
       grind)
    | (have r₁ := eq496 X1 X1
       have r₂ := eq2562 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq496 X0 X1
       have r₂ := eq2562 X0 (M.op X0 X1)
       grind)
    | exact resolve eq496 eq2562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496 eq2562
  have eq2595 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X1 ∨ X0 = X1 ∨ (τ (k X0 X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2583 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2583
  have eq2596 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2595 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2595
  have eq2626 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq2596 (σ X0) X1
       grind)
    | exact superpose eq2596 eq37
    | (have j1 := eq2596 (σ X0) X1
       grind)
    | exact resolve eq37 eq2596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq2629 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq2596 X0 X1
       grind)
    | exact superpose eq2596 eq11
    | (have j1 := eq2596 X0 X1
       grind)
    | exact resolve eq11 eq2596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2596
  have eq2695 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2629 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq2629
    | (have j0 := eq2629 X0 X1
       grind)
    | exact resolve eq2629 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2629
  have eq2748 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq2695 (τ X0) X1
       grind)
    | exact superpose eq2695 eq18
    | (have j1 := eq2695 (τ X0) X1
       grind)
    | exact resolve eq18 eq2695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2695
  have eq5152 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X1) X0
       have i₂ := eq2626 X1 (σ X0)
       grind)
    | exact superpose eq2626 eq28
    | (have j1 := eq2626 X0 (σ X1)
       grind)
    | exact resolve eq28 eq2626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2626
  have eq5212 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5152 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5152
    | (have j0 := eq5152 X0 X1
       grind)
    | exact resolve eq5152 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5152
  have eq5250 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5212 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5212
    | (have j0 := eq5212 X0 X1
       grind)
    | exact resolve eq5212 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5212
  have eq5263 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5250 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5250
    | (have j0 := eq5250 X0 X1
       grind)
    | exact resolve eq5250 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5250
  have eq5275 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2748 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2748
    | exact resolve eq2748 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2748
  have eq5340 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5275 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5275
    | (have j0 := eq5275 X0 X1
       grind)
    | exact resolve eq5275 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5275
  have eq5506 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq5263 X1 X0
       grind)
    | exact superpose eq5263 eq11
    | (have j1 := eq5263 X1 X0
       grind)
    | exact resolve eq11 eq5263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5263
  have eq6272 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5506 x y
       grind)
    | exact superpose eq5506 eq16
    | (have j1 := eq5506 x y
       grind)
    | exact resolve eq16 eq5506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5506
  have eq6350 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq6272
       have i₂ := eq992 x y
       grind)
    | exact superpose eq992 eq6272
    | (have j1 := eq992 x y
       grind)
    | (have r₁ := eq6272
       have r₂ := eq992 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq6272
       have r₂ := eq992 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6272 eq992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992 eq6272
  have eq6358 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq6350
  have eq6376 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6358
       grind)
    | exact superpose eq6358 eq16
    | exact resolve eq16 eq6358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6358
  have eq6377 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6376
       have r₂ := eq22 x
       grind)
    | exact resolve eq6376 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6376
  have eq6381 : x = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq120 x y
       have i₂ := eq6377
       grind)
    | exact superpose eq6377 eq120
    | exact resolve eq120 eq6377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6392 : x ≠ y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  have eq6406 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6381
       have i₂ := eq6377
       grind)
    | exact superpose eq6377 eq6381
    | exact resolve eq6381 eq6377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6377 eq6381
  have eq6421 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq6406
  have eq6425 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6421
       have r₂ := eq6392
       grind)
    | exact resolve eq6421 eq6392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6392 eq6421
  have eq17818 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1056
       have i₂ := eq6425
       grind)
    | exact superpose eq6425 eq1056
    | exact resolve eq1056 eq6425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056 eq6425
  have eq17838 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by grind
  clear eq17818
  have eq17839 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq17838
  have eq17847 : y = (τ (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq17839
       grind)
    | exact superpose eq17839 eq10
    | exact resolve eq10 eq17839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17839
  have eq17911 : x = y ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq17847
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq17847
    | exact resolve eq17847 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17847
  have eq17998 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17911
       grind)
    | exact superpose eq17911 eq16
    | exact resolve eq16 eq17911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17911
  have eq17999 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have r₁ := eq17998
       have r₂ := eq22 x
       grind)
    | exact resolve eq17998 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq17998
  have eq18015 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17999
       grind)
    | exact superpose eq17999 eq16
    | exact resolve eq16 eq17999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18025 : (σ x) = (M.op (σ x) (M.op (σ x) (σ (k x y)))) := by
    first
    | (have i₁ := eq120 (σ x) (σ y)
       have i₂ := eq17999
       grind)
    | exact superpose eq17999 eq120
    | exact resolve eq120 eq17999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq18120 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq18015
       have i₂ := eq5340 x y
       grind)
    | exact superpose eq5340 eq18015
    | (have j1 := eq5340 x y
       grind)
    | (have r₁ := eq18015
       have r₂ := eq5340 x y
       grind)
    | (have r₁ := eq18015
       have r₂ := eq5340 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq18015
       have r₂ := eq5340 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq18015 eq5340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5340
  have eq18121 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18015
       have i₂ := eq887 y x
       grind)
    | exact superpose eq887 eq18015
    | (have j1 := eq887 y x
       grind)
    | (have r₁ := eq18015
       have r₂ := eq887 y x
       grind)
    | (have r₁ := eq18015
       have r₂ := eq887 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq18015
       have r₂ := eq887 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq18015 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq18122 : x = y ∨ x = (M.op x y) := by grind
  clear eq18121
  have eq18123 : x = y ∨ y = (k x y) := by grind
  clear eq18120
  have eq18130 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18015
       have i₂ := eq18122
       grind)
    | exact superpose eq18122 eq18015
    | exact resolve eq18015 eq18122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18122
  have eq18131 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x y) := by grind
  clear eq18130
  have eq18132 : x = (M.op x y) := by grind
  clear eq18131
  have eq18220 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq18015
       have i₂ := eq18123
       grind)
    | exact superpose eq18123 eq18015
    | exact resolve eq18015 eq18123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18123
  have eq18224 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ y = (k x y) := by grind
  clear eq18220
  have eq18225 : y = (k x y) := by grind
  clear eq18224
  have eq18237 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq18015
       have i₂ := eq18225
       grind)
    | exact superpose eq18225 eq18015
    | exact resolve eq18015 eq18225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18015
  have eq18259 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq18237
       have i₂ := eq18132
       grind)
    | exact superpose eq18132 eq18237
    | exact resolve eq18237 eq18132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18132 eq18237
  have eq18405 : (σ x) = (M.op (σ x) (σ (k x (k x y)))) ∨ (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq18025
       have i₂ := eq551 x (k x y)
       grind)
    | exact superpose eq551 eq18025
    | (have j1 := eq551 x (k x y)
       grind)
    | exact resolve eq18025 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551 eq18025
  have eq18453 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq18405
       have i₂ := eq18225
       grind)
    | exact superpose eq18225 eq18405
    | exact resolve eq18405 eq18225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18405
  have eq18454 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq18453
  have eq18466 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq18454
       have i₂ := eq18225
       grind)
    | exact superpose eq18225 eq18454
    | exact resolve eq18454 eq18225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18454
  have eq18477 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq18466
       have i₂ := eq17999
       grind)
    | exact superpose eq17999 eq18466
    | exact resolve eq18466 eq17999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17999 eq18466
  have eq18478 : (σ x) = (σ (k x y)) := by grind
  clear eq18477
  have eq18487 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq18478
       have i₂ := eq18225
       grind)
    | exact superpose eq18225 eq18478
    | exact resolve eq18478 eq18225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18225 eq18478
  have eq18494 : False := by grind
  exact eq18494

/-- `Equation4301`: `x ◇ (x ◇ y) = z ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_y_pxx_pxy_Equation4301 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4301 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4301.models_iff G M).mp hM
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X0 X2)) := by
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
  have eq175 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X3)) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 (M.op X0 X2) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | (have i₁ := eq16 X0 (M.op X0 X1) X2
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op y (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq37 (M.op sF0 sF0)
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq37
    | exact resolve eq37 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq190 : (M.op x (M.op x y)) = (M.op y (M.op x y)) := by
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
  have eq191 : ∀ X0 X1 : G, (M.op x (M.op x y)) = (M.op (M.op x X1) (M.op X0 (M.op x X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op x X1)
       have i₂ := eq16 x X1 X0
       grind)
    | (have i₁ := eq175 (M.op X0 x)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op (M.op x X1) (M.op x (M.op x y))) := by
    intro X1
    first
    | (have i₁ := eq191 x X1
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq191
    | exact resolve eq191 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq202 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ y)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op x (σ x)) (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq176 (M.op x sF2)
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq176
    | exact resolve eq176 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq214 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq200 eq205
    | exact resolve eq205 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq216 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq202 eq16
    | exact resolve eq16 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq176 eq216
    | exact resolve eq216 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq216
  have eq225 : ∀ X0 X1 : G, (M.op y (M.op x y)) = (M.op x (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq181 (M.op X0 x)
       have i₂ := eq16 X0 X1 x
       grind)
    | (have i₁ := eq181 (M.op x X1)
       have i₂ := eq16 x X1 x
       grind)
    | exact superpose eq16 eq181
    | exact resolve eq181 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq243 : ∀ X0 X1 : G, (M.op x (M.op x y)) = (M.op x (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq190 eq225
    | exact resolve eq225 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq225
  have eq249 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op x (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq214 eq243
    | exact resolve eq243 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq330 : (τ (M.op (σ x) (σ x))) = (k x (τ (M.op (σ x) (σ x)))) := by
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
  have eq431 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (M.op (σ y) X1)) := by
    intro X1
    first
    | exact superpose eq218 eq16
    | exact resolve eq16 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq433 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (σ y) X1) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq218 eq16
    | exact resolve eq16 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq435 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) X1) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X1
    first
    | exact superpose eq218 eq433
    | exact resolve eq433 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq433
  have eq490 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ y) X0) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq431 eq16
    | exact resolve eq16 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq435 eq490
    | exact resolve eq490 eq435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435 eq490
  have eq573 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq431 eq503
    | exact resolve eq503 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq595 : ∀ X0 X2 : G, (M.op X2 (M.op X0 X2)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X2
    first
    | (have i₁ := eq16 X0 x X2
       have i₂ := eq503 X0 x
       grind)
    | (have i₁ := eq16 (σ x) (σ y) X2
       have i₂ := eq503 X0 x
       grind)
    | exact superpose eq503 eq16
    | exact resolve eq16 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq664 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq573 eq174
    | exact resolve eq174 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq573
  have eq694 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq702 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq753 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq754 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq755 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq754 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq4655 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq694
       grind)
    | exact superpose eq694 eq40
    | exact resolve eq40 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq4656 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4655
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4655
    | exact resolve eq4655 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4655
  have eq4658 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq4656
    | exact resolve eq4656 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4656
  have eq6265 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq4658 eq702
    | exact resolve eq702 eq4658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4658
  have eq6272 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq6265
       have r₂ := eq27
       grind)
    | exact resolve eq6265 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6265
  have eq6277 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq6272 eq330
    | exact resolve eq330 eq6272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330 eq6272
  have eq6323 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq6277
    | exact resolve eq6277 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6277
  have eq6335 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq6323
       have r₂ := eq13 x y
       grind)
    | exact resolve eq6323 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6323
  have eq6342 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq694
       have i₂ := eq6335
       grind)
    | exact superpose eq6335 eq694
    | exact resolve eq694 eq6335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq6343 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq6335
       grind)
    | exact superpose eq6335 eq35
    | exact resolve eq35 eq6335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq6335
  have eq6345 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq6342
  have eq6348 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6343
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6343
    | exact resolve eq6343 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6343
  have eq6370 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X1 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq178 x x X1 X0
       have i₂ := eq6345
       grind)
    | exact superpose eq6345 eq178
    | exact resolve eq178 eq6345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq6384 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq595 x x
       have i₂ := eq6345
       grind)
    | exact superpose eq6345 eq595
    | exact resolve eq595 eq6345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6345
  have eq6387 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6384
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6384
    | exact resolve eq6384 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6384
  have eq6399 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X1 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq6370 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6370
    | (have j0 := eq6370 X0 X1
       grind)
    | exact resolve eq6370 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6370
  have eq6422 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq6399 x X1
       have i₂ := eq595 X1 x
       grind)
    | exact superpose eq595 eq6399
    | exact resolve eq6399 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6399
  have eq6436 : ∀ X1 : G, (M.op x y) = (M.op X1 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq6387 eq6422
    | exact resolve eq6422 eq6387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6422
  have eq6447 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6348 eq702
    | exact resolve eq702 eq6348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq6348
  have eq6451 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq6447
  have eq6702 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6436 eq189
    | exact resolve eq189 eq6436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6436
  have eq6723 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq6702
    | exact resolve eq6702 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6702
  have eq6801 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6451 eq595
    | exact resolve eq595 eq6451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6451
  have eq6804 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq6801
    | exact resolve eq6801 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6801
  have eq6821 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6387 eq6804
    | exact resolve eq6804 eq6387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6804
  have eq6868 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6821 eq664
    | exact resolve eq664 eq6821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq6870 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq6872 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq6868
    | exact resolve eq6868 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6868
  have eq6889 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6821 eq6872
    | exact resolve eq6872 eq6821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6872
  have eq6926 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6723 eq755
    | (have j0 := eq755 (σ (M.op x y))
       grind)
    | (have r₁ := eq755 (σ (M.op x y))
       have r₂ := eq6723
       grind)
    | exact resolve eq755 eq6723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6723
  have eq6927 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq6926
  have eq6933 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6889 eq152
    | exact resolve eq152 eq6889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq6889
  have eq6936 : y = (k y y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq6933
    | exact resolve eq6933 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq6933
  have eq7195 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6927 eq595
    | exact resolve eq595 eq6927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7197 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6387 eq7195
    | exact resolve eq7195 eq6387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6387 eq7195
  have eq9615 : y ≠ y ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq755 y
       have i₂ := eq6936
       grind)
    | exact superpose eq6936 eq755
    | (have j0 := eq755 y
       grind)
    | (have r₁ := eq755 y
       have r₂ := eq6936
       grind)
    | exact resolve eq755 eq6936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755 eq6936
  have eq9616 : y = (M.op y y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq9615
  have eq9621 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7197 eq6927
    | exact resolve eq6927 eq7197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6927 eq7197
  have eq9649 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq9621
  have eq10185 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op x (M.op y y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq249 y y
       have i₂ := eq9616
       grind)
    | exact superpose eq9616 eq249
    | exact resolve eq249 eq9616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq10195 : (M.op (σ x) (σ y)) = (M.op x (M.op y y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6821 eq10185
    | exact resolve eq10185 eq6821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10185
  have eq10216 : (M.op (σ x) (σ y)) = (M.op x (M.op y y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq10195
    | exact resolve eq10195 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10195
  have eq10235 : (σ y) = (M.op x (M.op y y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6821 eq10216
    | exact resolve eq10216 eq6821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6821 eq10216
  have eq10251 : (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9616 eq10235
    | exact resolve eq10235 eq9616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9616 eq10235
  have eq10265 : (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10251
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10251
    | exact resolve eq10251 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10251
  have eq10271 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10265
       have r₂ := eq6870
       grind)
    | exact resolve eq10265 eq6870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6870 eq10265
  have eq10274 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10271 eq27
    | exact resolve eq27 eq10271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10293 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10271 eq9649
    | exact resolve eq9649 eq10271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9649
  have eq10294 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq10293
  have eq10304 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq10294 eq26
    | exact resolve eq26 eq10294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10316 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq10294 eq202
    | exact resolve eq202 eq10294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq10294
  have eq10347 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10316
       have r₂ := eq10274
       grind)
    | exact resolve eq10316 eq10274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10316
  have eq10359 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10304
       have r₂ := eq10274
       grind)
    | exact resolve eq10304 eq10274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10304
  have eq10361 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10271 eq10347
    | exact resolve eq10347 eq10271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10347
  have eq10368 : (M.op x y) = (M.op (σ x) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10271 eq10359
    | exact resolve eq10359 eq10271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10359
  have eq10559 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10361 eq10368
    | exact resolve eq10368 eq10361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10368
  have eq10589 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq10559
  have eq10651 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10589 eq189
    | exact resolve eq189 eq10589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10696 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq10651
    | exact resolve eq10651 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10651
  have eq10906 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10696 eq753
    | (have j0 := eq753 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq753 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq10696
       grind)
    | exact resolve eq753 eq10696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10696
  have eq10907 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq10906
  have eq10908 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq10907
  have eq10941 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10908 eq595
    | exact resolve eq595 eq10908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10947 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10271 eq10941
    | exact resolve eq10941 eq10271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10271 eq10941
  have eq10968 : (M.op (M.op x y) (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10361 eq10947
    | exact resolve eq10947 eq10361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10361 eq10947
  have eq10987 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10589 eq10968
    | exact resolve eq10968 eq10589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10589 eq10968
  have eq11030 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10987 eq10908
    | exact resolve eq10908 eq10987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10908 eq10987
  have eq11060 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq11030
  have eq11086 : y = (M.op x y) := by
    first
    | (have r₁ := eq11060
       have r₂ := eq10274
       grind)
    | exact resolve eq11060 eq10274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10274 eq11060
  have eq11108 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11086
       grind)
    | exact superpose eq11086 eq18
    | exact resolve eq18 eq11086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq11109 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq11086
       grind)
    | exact superpose eq11086 eq24
    | exact resolve eq24 eq11086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq11086
  have eq11118 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq11109 eq20
    | exact resolve eq20 eq11109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11109
  have eq11198 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq11108 eq214
    | exact resolve eq214 eq11108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq11203 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq11108 eq200
    | exact resolve eq200 eq11108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq11108
  have eq11307 : (M.op x y) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq11198 eq503
    | exact resolve eq503 eq11198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq11344 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq11203 eq189
    | exact resolve eq189 eq11203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq11203
  have eq11382 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq11344
    | exact resolve eq11344 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq11344
  have eq11390 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq11118 eq11382
    | exact resolve eq11382 eq11118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11382
  have eq11693 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq11390 eq753
    | (have j0 := eq753 (σ y) (σ y)
       grind)
    | (have r₁ := eq753 (σ y) (σ y)
       have r₂ := eq11390
       grind)
    | exact resolve eq753 eq11390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753 eq11390
  have eq11694 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq11693
  have eq11695 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq11694
  have eq11732 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq11695 eq595
    | exact resolve eq595 eq11695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq11734 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq11695 eq11732
    | exact resolve eq11732 eq11695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11695 eq11732
  have eq11754 : (M.op x y) = (σ y) := by
    first
    | exact superpose eq11198 eq11734
    | exact resolve eq11734 eq11198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11198 eq11734
  have eq11792 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq11754 eq26
    | exact resolve eq26 eq11754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq11840 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11307 eq11792
    | exact resolve eq11792 eq11307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11307 eq11792
  have eq11861 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq11840 eq27
    | exact resolve eq27 eq11840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq11840
  have eq11900 : (M.op x y) ≠ (σ y) := by
    first
    | exact superpose eq11118 eq11861
    | exact resolve eq11861 eq11118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11118 eq11861
  have eq11904 : False := by grind
  exact eq11904

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_x_pxx_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
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
  have eq60 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq14 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq14 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq60 (M.op X1 X0) X0
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq60
    | exact resolve eq60 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq75
    | exact resolve eq75 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq80
    | exact resolve eq80 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq86 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X1) X0 X1
       have i₂ := eq61 (M.op X1 X1) X0
       grind)
    | exact superpose eq61 eq14
    | exact resolve eq14 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq61 X0 (M.op X0 X0)
       grind)
    | exact superpose eq61 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq61 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq88 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq341 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq394 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq70 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq395 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq394 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq504 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq341 X0 (M.op X1 X1)
       have i₂ := eq90 X1 (σ X0)
       grind)
    | exact superpose eq90 eq341
    | exact resolve eq341 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq526 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq504 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq504
    | exact resolve eq504 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq3237 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq395 (M.op X0 X0)
       have i₂ := eq90 X0 (M.op X0 X0)
       grind)
    | exact superpose eq90 eq395
    | (have j0 := eq395 (M.op X0 X0)
       grind)
    | exact resolve eq395 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq3249 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq395 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq395
    | (have j0 := eq395 (τ X0)
       grind)
    | exact resolve eq395 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq395
  have eq3261 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq3237 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3237
  have eq3266 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3249 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3249
    | (have j0 := eq3249 X0
       grind)
    | exact resolve eq3249 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3249
  have eq3276 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3266 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3266
    | (have j0 := eq3266 X0
       grind)
    | exact resolve eq3266 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3266
  have eq18736 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 (σ (M.op X0 X0)) X1
       have i₂ := eq3261 X0
       grind)
    | exact superpose eq3261 eq61
    | exact resolve eq61 eq3261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18737 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 (σ (M.op X0 X0))
       have i₂ := eq3261 X0
       grind)
    | exact superpose eq3261 eq86
    | exact resolve eq86 eq3261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3261
  have eq19499 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq81 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq19500 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq19499
    | exact resolve eq19499 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19499
  have eq19511 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq19500
       have r₂ := eq28
       grind)
    | exact resolve eq19500 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19500
  have eq19522 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq19511 eq526
    | exact resolve eq526 eq19511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19511
  have eq19543 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq30 eq19522
    | exact resolve eq19522 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq19522
  have eq19544 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ y)) ∨ (k X0 y) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq19543 X0
       have j1 := eq13 X0 y
       grind)
    | (have r₁ := eq19543 X0
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq19543 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19543
  have eq19549 : ∀ X0 X1 : G, x = (M.op y y) ∨ (k X1 y) = X1 ∨ (M.op X0 (σ x)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1
       have i₂ := eq19544 (M.op X0 X0)
       grind)
    | exact superpose eq19544 eq61
    | (have j1 := eq19544 X1
       grind)
    | exact resolve eq61 eq19544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19569 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 y) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq65 X0 x
       have i₂ := eq19544 (M.op x X0)
       grind)
    | exact superpose eq19544 eq65
    | (have j1 := eq19544 X0
       grind)
    | exact resolve eq65 eq19544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19544
  have eq19572 : ∀ X0 : G, x = (M.op y y) ∨ (k X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq19569
    | (have j0 := eq19569 X0
       grind)
    | exact resolve eq19569 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19569
  have eq19598 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) X0) ∨ (k X1 y) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq18737 y X1
       have i₂ := eq19572 X0
       grind)
    | exact superpose eq19572 eq18737
    | (have j1 := eq19572 X1
       grind)
    | exact resolve eq18737 eq19572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18737 eq19572
  have eq19608 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) X0) ∨ (k X1 y) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq19598 X0 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19598
    | (have j0 := eq19598 X0 X1
       grind)
    | exact resolve eq19598 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19598
  have eq23146 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq27
       have i₂ := eq19608 X0 (M.op sF2 sF3)
       grind)
    | exact superpose eq19608 eq27
    | (have j1 := eq19608 (σ y) X0
       grind)
    | exact resolve eq27 eq19608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19608
  have eq23177 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq23146 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23146
  have eq23234 : y ≠ y ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3276 y
       have i₂ := eq23177 y
       grind)
    | exact superpose eq23177 eq3276
    | (have j0 := eq3276 y
       grind)
    | (have r₁ := eq3276 y
       have r₂ := eq23177 y
       grind)
    | exact resolve eq3276 eq23177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23177
  have eq23271 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23234
  have eq23523 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq18736 y X0
       have i₂ := eq23271
       grind)
    | exact superpose eq23271 eq18736
    | exact resolve eq18736 eq23271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18736 eq23271
  have eq23537 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq23523 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq23523
    | (have j0 := eq23523 X0
       grind)
    | exact resolve eq23523 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq23523
  have eq24388 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23537 eq27
    | (have j1 := eq23537 (σ x)
       grind)
    | exact resolve eq27 eq23537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq23537
  have eq24390 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24388
  have eq24400 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq24390 eq28
    | exact resolve eq28 eq24390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq24390
  have eq47831 : ∀ X0 X1 : G, x = (M.op x y) ∨ (k X0 y) = X0 ∨ (M.op X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 y y
       have i₂ := eq19549 X0 X1
       grind)
    | exact superpose eq19549 eq65
    | (have j1 := eq19549 X1 X0
       grind)
    | exact resolve eq65 eq19549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq19549
  have eq47833 : ∀ X0 X1 : G, (k X0 y) = X0 ∨ x = (M.op x y) ∨ (M.op X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47831 X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq47831
    | (have j0 := eq47831 X0 X1
       grind)
    | exact resolve eq47831 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47831
  have eq47925 : ∀ X0 : G, y ≠ y ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3276 y
       have i₂ := eq47833 y X0
       grind)
    | exact superpose eq47833 eq3276
    | (have j0 := eq3276 y
       have j1 := eq47833 X0 X0
       grind)
    | (have r₁ := eq3276 y
       have r₂ := eq47833 y x
       grind)
    | exact resolve eq3276 eq47833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47833
  have eq48001 : ∀ X0 : G, y = (M.op y y) ∨ x = (M.op x y) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq47925 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47925
  have eq48240 : ∀ X0 X1 : G, (M.op X1 (σ x)) = X1 ∨ x = (M.op x y) ∨ (M.op X0 y) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq61 y X0
       have i₂ := eq48001 X1
       grind)
    | exact superpose eq48001 eq61
    | (have j1 := eq48001 X1
       grind)
    | exact resolve eq61 eq48001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48001
  have eq49300 : ∀ X0 X1 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op x y) ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq526 X0 X1
       have i₂ := eq48240 (M.op X1 X1) X1
       grind)
    | exact superpose eq48240 eq526
    | (have j1 := eq48240 x X1
       grind)
    | exact resolve eq526 eq48240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526 eq48240
  have eq49322 : ∀ X0 X1 : G, (k X0 x) = X0 ∨ x = (M.op x y) ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | exact superpose eq29 eq49300
    | (have j0 := eq49300 X0 x
       grind)
    | exact resolve eq49300 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq49300
  have eq51919 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq3276 x
       have i₂ := eq49322 x X0
       grind)
    | exact superpose eq49322 eq3276
    | (have j0 := eq3276 x
       have j1 := eq49322 X0 x
       grind)
    | (have r₁ := eq3276 x
       have r₂ := eq49322 x x
       grind)
    | exact resolve eq3276 eq49322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3276 eq49322
  have eq52003 : ∀ X0 : G, x = (M.op x x) ∨ x = (M.op x y) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq51919 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51919
  have eq55594 : ∀ X0 X1 : G, (M.op X1 y) = X1 ∨ x = (M.op x y) ∨ (M.op X0 x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq61 x X0
       have i₂ := eq52003 X1
       grind)
    | exact superpose eq52003 eq61
    | (have j1 := eq52003 X1
       grind)
    | exact resolve eq61 eq52003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq52003
  have eq56785 : ∀ X0 : G, x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq19
       have i₂ := eq55594 X0 x
       grind)
    | exact superpose eq55594 eq19
    | (have j1 := eq55594 X0 x
       grind)
    | exact resolve eq19 eq55594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55594
  have eq56788 : ∀ X0 : G, (M.op X0 x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq56785 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56785
  have eq56806 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq86 X0 x
       have i₂ := eq56788 x
       grind)
    | exact superpose eq56788 eq86
    | exact resolve eq86 eq56788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq56788
  have eq56843 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq56806 y
       grind)
    | exact superpose eq56806 eq19
    | (have j1 := eq56806 y
       grind)
    | exact resolve eq19 eq56806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq56806
  have eq56883 : x = (M.op x y) := by grind
  clear eq56843
  have eq56899 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq56883 eq21
    | exact resolve eq21 eq56883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq56883
  have eq57129 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq56899
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq56899
    | exact resolve eq56899 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq56899
  have eq57136 : False := by grind
  exact eq57136

/-- `Equation4399`: `x ◇ (x ◇ y) = (x ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_y_pxy_x_pxy_Equation4399 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4399 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4399.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
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
  have eq52 : (M.op x (M.op x y)) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : y ≠ (M.op x y) ∨ x = (M.op x x) ∨ x = (k x y) := by
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
  have eq70 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq79 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq95 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq79 eq16
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq85
    | (have j0 := eq85 (σ X0) (σ X1)
       grind)
    | exact resolve eq85 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq85 x y
       grind)
    | exact superpose eq85 eq44
    | (have j1 := eq85 x y
       grind)
    | exact resolve eq44 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq105
    | exact resolve eq105 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq114
    | exact resolve eq114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq117 eq85
    | (have j0 := eq85 (σ x) (σ y)
       grind)
    | exact resolve eq85 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq124
    | exact resolve eq124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq128 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq125
       have r₂ := eq27
       grind)
    | exact resolve eq125 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq130 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq128
    | exact resolve eq128 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq185 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq85 (σ X0) sF3
       grind)
    | exact superpose eq85 eq40
    | (have j1 := eq85 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq85 (σ X0) sF1
       grind)
    | exact superpose eq85 eq41
    | (have j1 := eq85 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq41 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq34
  have eq331 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq496 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq130 eq70
    | (have r₁ := eq70
       have r₂ := eq130
       grind)
    | exact resolve eq70 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq130
  have eq497 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq496
  have eq522 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq497 eq117
    | exact resolve eq117 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq525 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq522
  have eq532 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq525 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq525
       grind)
    | exact resolve eq13 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq533 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq532 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq566 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq533 eq117
    | exact resolve eq117 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq533
  have eq568 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq566
  have eq573 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq568
    | exact resolve eq568 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq575 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq573
       have r₂ := eq27
       grind)
    | exact resolve eq573 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq596 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq575 eq28
    | exact resolve eq28 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq575
  have eq614 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq596
    | exact resolve eq596 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq615 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq614 eq20
    | exact resolve eq20 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq616 : (σ (k x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq614 eq45
    | exact resolve eq45 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq617 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq614 eq52
    | exact resolve eq52 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq618 : y ≠ y ∨ x = (M.op x x) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq614 eq68
    | (have r₁ := eq68
       have r₂ := eq614
       grind)
    | exact resolve eq68 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq619 : (σ (k y y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq614 eq79
    | exact resolve eq79 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq621 : x = (k x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq618
  have eq622 : (k (σ y) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq619
       have i₂ := eq78
       grind)
    | exact superpose eq78 eq619
    | exact resolve eq619 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq623 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq617
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq617
    | exact resolve eq617 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq624 : (k (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq616
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq616
    | exact resolve eq616 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq625 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq615
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq615
    | exact resolve eq615 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq668 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq97 X0 X0
       grind)
    | exact superpose eq97 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq97 X0 X0
       grind)
    | (have r₁ := eq13 (σ X1) X1
       have r₂ := eq97 X1 X1
       grind)
    | exact resolve eq13 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq97 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq670 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq668 X0 X1
       have j1 := eq13 (σ X0) X1
       grind)
    | (have r₁ := eq668 X0 X1
       have r₂ := eq13 (σ X0) X1
       grind)
    | exact resolve eq668 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq678 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq625 eq40
    | exact resolve eq40 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq704 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq41 eq678
    | exact resolve eq678 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq678
  have eq722 : (M.op (M.op x y) y) = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq623
       grind)
    | exact superpose eq623 eq14
    | exact resolve eq14 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq723 : ∀ X0 : G, y ≠ (M.op x y) ∨ (k y X0) = (M.op y X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq623
       grind)
    | exact superpose eq623 eq13
    | (have j0 := eq13 y X0
       grind)
    | exact resolve eq13 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq724 : ∀ X0 : G, (k y X0) = (M.op y X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq723 X0
       grind)
    | (have r₁ := eq723 X0
       have r₂ := eq614
       grind)
    | exact resolve eq723 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq725 : (M.op x (M.op x y)) = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq52 eq722
    | exact resolve eq722 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq764 : (k y y) = (τ (k (σ y) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq622 eq90
    | exact resolve eq90 eq622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq768 : (k y y) = (k y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq95 eq764
    | exact resolve eq764 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq764
  have eq778 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq624 eq85
    | (have j0 := eq85 (σ x) (σ y)
       grind)
    | exact resolve eq85 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq624
  have eq779 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq778
    | exact resolve eq778 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq782 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq779
    | exact resolve eq779 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq870 : ∀ X0 : G, (σ (M.op y (τ X0))) = (k (σ y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq38 X0 y
       have i₂ := eq724 (τ X0)
       grind)
    | exact superpose eq724 eq38
    | exact resolve eq38 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq873 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq724 y
       grind)
    | exact superpose eq724 eq78
    | exact resolve eq78 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq876 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op y (τ X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq870 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq870
    | (have j0 := eq870 X0
       grind)
    | exact resolve eq870 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq925 : (k y y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq768 eq724
    | exact resolve eq724 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq927 : (k y y) = (M.op y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq925
  have eq1001 : (M.op y y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq724 y
       have i₂ := eq927
       grind)
    | exact superpose eq927 eq724
    | exact resolve eq724 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724 eq927
  have eq1003 : (M.op y y) = (M.op y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq1001
  have eq1018 : (M.op x (M.op x y)) = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1003 eq725
    | exact resolve eq725 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725 eq1003
  have eq1025 : (M.op x (M.op x y)) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq1018
  have eq1140 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq250 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq250
    | exact resolve eq250 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1158 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq250 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq250
    | (have j0 := eq250 X0 y
       grind)
    | exact resolve eq250 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1159 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20 eq250
    | (have j0 := eq250 X0 (M.op x y)
       grind)
    | exact resolve eq250 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq1369 : (k x (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq782 eq63
    | exact resolve eq63 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq1404 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq873
       have i₂ := eq623
       grind)
    | exact superpose eq623 eq873
    | exact resolve eq873 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623 eq873
  have eq1420 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1404
  have eq1423 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1420
    | exact resolve eq1420 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420
  have eq1435 : (τ (σ (M.op x y))) = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1423 eq90
    | exact resolve eq90 eq1423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq1423
  have eq1446 : (M.op x y) = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq1435
    | exact resolve eq1435 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435
  have eq2454 : ∀ X0 : G, (σ y) ≠ (σ (k X0 y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq185 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq2552 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k X0 (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq205 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq3443 : (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq669 x y
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq669
    | (have j0 := eq669 x y
       grind)
    | exact resolve eq669 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3481 : (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3443
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3443
    | exact resolve eq3443 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3443
  have eq3522 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq3481
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3481
    | exact resolve eq3481 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3481
  have eq3554 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq3522
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3522
    | exact resolve eq3522 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3522
  have eq3571 : (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3554
    | exact resolve eq3554 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3554
  have eq10619 : (σ (M.op x y)) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq625 eq3571
    | exact resolve eq3571 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3571
  have eq10626 : (σ (M.op x y)) ≠ (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10619
       have r₂ := eq27
       grind)
    | exact resolve eq10619 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10619
  have eq11078 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq614 eq1159
    | exact resolve eq1159 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614 eq1159
  have eq11109 : ∀ X0 : G, (τ (k X0 (σ y))) = (τ (k X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq11078 X0
       have i₂ := eq1158 X0
       grind)
    | exact superpose eq1158 eq11078
    | exact resolve eq11078 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158 eq11078
  have eq11869 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq669 (τ X0) (τ X1)
       have i₂ := eq1140 X1 X0
       grind)
    | exact superpose eq1140 eq669
    | (have j0 := eq669 (τ X0) (τ X1)
       grind)
    | exact resolve eq669 eq1140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669 eq1140
  have eq11876 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11869 X0 X1
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq11869
    | (have j0 := eq11869 X0 X1
       grind)
    | exact resolve eq11869 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11869
  have eq11900 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11876 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq11876
    | (have j0 := eq11876 X0 X1
       grind)
    | exact resolve eq11876 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11876
  have eq11920 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11900 X0 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq11900
    | (have j0 := eq11900 X0 X1
       grind)
    | exact resolve eq11900 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11900
  have eq11928 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11920 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq11920
    | (have j0 := eq11920 X0 X1
       grind)
    | exact resolve eq11920 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11920
  have eq22697 : ∀ X0 : G, (k X0 (τ (σ y))) = (τ (k (σ X0) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11109 eq331
    | exact resolve eq331 eq11109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11109
  have eq22779 : ∀ X0 : G, (k X0 (τ (σ (M.op x y)))) = (k X0 (τ (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22697 X0
       have i₂ := eq331 X0 sF1
       grind)
    | exact superpose eq331 eq22697
    | exact resolve eq22697 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331 eq22697
  have eq22799 : ∀ X0 : G, (k X0 y) = (k X0 (τ (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq22779
    | exact resolve eq22779 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq22779
  have eq22808 : ∀ X0 : G, (k X0 y) = (k X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30 eq22799
    | exact resolve eq22799 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq22799
  have eq40217 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq876 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq876
    | exact resolve eq876 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876
  have eq40368 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq36 eq40217
    | exact resolve eq40217 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq40217
  have eq40688 : (σ (k x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1369 eq704
    | exact resolve eq704 eq1369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369
  have eq40702 : (σ (k x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq40688
  have eq40714 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40702
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq40702
    | exact resolve eq40702 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40702
  have eq40732 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40714
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq40714
    | exact resolve eq40714 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40714
  have eq40759 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq625 eq40732
    | exact resolve eq40732 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40732
  have eq40803 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq40759
  have eq40805 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq40803
       have r₂ := eq27
       grind)
    | exact resolve eq40803 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40803
  have eq40814 : (k x (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq40805 eq63
    | exact resolve eq63 eq40805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq40805
  have eq40851 : (σ (k x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq40814 eq704
    | exact resolve eq704 eq40814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq40852 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq40814 eq22808
    | exact resolve eq22808 eq40814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22808 eq40814
  have eq40864 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq40852
  have eq40865 : (σ (k x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by grind
  clear eq40851
  have eq40877 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40865
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq40865
    | exact resolve eq40865 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40865
  have eq40895 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40877
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq40877
    | exact resolve eq40877 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40877
  have eq88096 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40368 y
       have i₂ := eq1446
       grind)
    | exact superpose eq1446 eq40368
    | exact resolve eq40368 eq1446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446 eq40368
  have eq88301 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by grind
  clear eq88096
  have eq88379 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq88301
    | exact resolve eq88301 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88301
  have eq88393 : (σ (M.op x y)) = (σ (M.op x (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq88379
       have i₂ := eq1025
       grind)
    | exact superpose eq1025 eq88379
    | exact resolve eq88379 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025 eq88379
  have eq88515 : (σ (M.op x y)) = (σ (M.op x (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq88393
  have eq846483 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq621
       grind)
    | exact superpose eq621 eq44
    | exact resolve eq44 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq846502 : x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40864
       have i₂ := eq621
       grind)
    | exact superpose eq621 eq40864
    | exact resolve eq40864 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621 eq40864
  have eq846562 : x = (M.op x x) ∨ x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq846502
  have eq846629 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq846483
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq846483
    | exact resolve eq846483 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846483
  have eq875645 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq846629 eq40895
    | exact resolve eq40895 eq846629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40895 eq846629
  have eq875714 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq875645
  have eq875743 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq875714
       grind)
    | exact superpose eq875714 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq875714
       grind)
    | exact resolve eq13 eq875714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875714
  have eq875755 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq875743 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875743
  have eq2838750 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2454 x
       have i₂ := eq875755 y
       grind)
    | exact superpose eq875755 eq2454
    | (have j0 := eq2454 x
       grind)
    | exact resolve eq2454 eq875755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2454 eq875755
  have eq2839058 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2838750
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2838750
    | exact resolve eq2838750 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2838750
  have eq2839627 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq2839058
    | exact resolve eq2839058 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2839058
  have eq2839998 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2839627
       have r₂ := eq625
       grind)
    | exact resolve eq2839627 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2839627
  have eq2840093 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2839998
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2839998
    | exact resolve eq2839998 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2839998
  have eq2840132 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq2840093
    | exact resolve eq2840093 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2840093
  have eq2840162 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2840132 eq27
    | exact resolve eq27 eq2840132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2840132
  have eq2841108 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2840162
       have r₂ := eq625
       grind)
    | exact resolve eq2840162 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625 eq2840162
  have eq2841123 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2841108 eq53
    | exact resolve eq53 eq2841108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq2842114 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2841123
    | exact resolve eq2841123 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2841123
  have eq2842130 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2842114 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | exact resolve eq13 eq2842114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2842169 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2842130 X0
       grind)
    | (have r₁ := eq2842130 X0
       have r₂ := eq2841108
       grind)
    | exact resolve eq2842130 eq2841108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2841108 eq2842130
  have eq2843234 : (σ (M.op x y)) ≠ (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2842169 eq10626
    | exact resolve eq10626 eq2842169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10626
  have eq2843292 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2842169 eq49
    | exact resolve eq49 eq2842169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq2842169
  have eq2843534 : (σ (M.op x y)) ≠ (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq2843234
  have eq2845698 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2842114 eq2843292
    | exact resolve eq2843292 eq2842114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2842114 eq2843292
  have eq2846363 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq2845698
  have eq2846564 : x ≠ (τ (M.op (σ x) (σ y))) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11928 x x
       have i₂ := eq2846363
       grind)
    | exact superpose eq2846363 eq11928
    | (have j0 := eq11928 x x
       grind)
    | exact resolve eq11928 eq2846363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11928 eq2846363
  have eq2846575 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2846564
       have r₂ := eq846562
       grind)
    | exact resolve eq2846564 eq846562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846562 eq2846564
  have eq2847220 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq2846575
       grind)
    | exact superpose eq2846575 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq2846575
       grind)
    | exact resolve eq13 eq2846575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2846575
  have eq2847248 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2847220 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2847220
  have eq2855215 : (σ (M.op x y)) ≠ (σ (M.op x (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2552 x
       have i₂ := eq2847248 sF0
       grind)
    | exact superpose eq2847248 eq2552
    | (have j0 := eq2552 x
       grind)
    | exact resolve eq2552 eq2847248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2552 eq2847248
  have eq2855392 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2855215
       have r₂ := eq88515
       grind)
    | exact resolve eq2855215 eq88515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88515 eq2855215
  have eq2855966 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2855392
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2855392
    | exact resolve eq2855392 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2855392
  have eq2856345 : x = (M.op x y) := by
    first
    | (have r₁ := eq2855966
       have r₂ := eq2843534
       grind)
    | exact resolve eq2855966 eq2843534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2843534 eq2855966
  have eq2856501 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2856345 eq20
    | exact resolve eq20 eq2856345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2856503 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq2856345 eq52
    | exact resolve eq52 eq2856345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq2857716 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2856503
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2856503
    | exact resolve eq2856503 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2856503
  have eq2857718 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2856501
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2856501
    | exact resolve eq2856501 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2856501
  have eq2857719 : x = (M.op x x) := by
    first
    | exact superpose eq2856345 eq2857716
    | exact resolve eq2857716 eq2856345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2856345 eq2857716
  have eq2857721 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2857718 eq26
    | exact resolve eq26 eq2857718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2858715 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq2857719
       grind)
    | exact superpose eq2857719 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq2857719
       grind)
    | exact resolve eq13 eq2857719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2858743 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq2858715 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2858715
  have eq2859081 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq670 x X0
       have i₂ := eq2858743 x
       grind)
    | exact superpose eq2858743 eq670
    | (have j0 := eq670 x X0
       grind)
    | exact resolve eq670 eq2858743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq2859981 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq2858743 y
       grind)
    | exact superpose eq2858743 eq44
    | exact resolve eq44 eq2858743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq2858743
  have eq2860516 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2857718 eq2859981
    | exact resolve eq2859981 eq2857718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2859981
  have eq2861281 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq2859081 X0
       have i₂ := eq2857719
       grind)
    | exact superpose eq2857719 eq2859081
    | (have j0 := eq2859081 X0
       grind)
    | exact resolve eq2859081 eq2857719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2857719 eq2859081
  have eq2861282 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq2861281 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2861281
  have eq2861546 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq2860516
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2860516
    | exact resolve eq2860516 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2860516
  have eq2862247 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq2861282 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2861282
    | (have j0 := eq2861282 X0
       grind)
    | exact resolve eq2861282 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2861282
  have eq2862484 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq2861546
    | exact resolve eq2861546 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2861546
  have eq2863044 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq2857718 eq2862247
    | exact resolve eq2862247 eq2857718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2857718 eq2862247
  have eq2868849 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2863044 eq2862484
    | exact resolve eq2862484 eq2863044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2862484 eq2863044
  have eq2868959 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2857721 eq2868849
    | exact resolve eq2868849 eq2857721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2857721 eq2868849
  have eq2869734 : False := by grind
  exact eq2869734

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxx_x_pxy_Equation4430 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4430 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X3) := by
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
  have eq50 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq14 X2 (M.op X2 x) X4 X5
       have i₂ := eq14 X2 x X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X4 X5 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X4 X5) X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq14 x x X4 X5
       have i₂ := eq14 x x X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X2 X3 (M.op x X5) X5
       have i₂ := eq14 X0 X1 x X5
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) y) := by
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
  have eq56 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq89 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
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
  clear eq44
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq114
    | exact resolve eq114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq194 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq214 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq55 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55
    | (have j0 := eq55 x y
       grind)
    | exact resolve eq55 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq229 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq214 eq228
    | exact resolve eq228 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq259 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq34
  have eq391 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq411 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq229 eq391
    | exact resolve eq391 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq488 : ∀ X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op x (M.op x y))) := by
    intro X2 X4 X5
    first
    | (have i₁ := eq50 x x X2 X4 X5
       have i₂ := eq411 x x
       grind)
    | exact superpose eq411 eq50
    | exact resolve eq50 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq489 : ∀ X2 : G, (M.op x (M.op x y)) = (M.op X2 (M.op x (M.op x y))) := by
    intro X2
    first
    | (have i₁ := eq488 X2 x x
       have i₂ := eq411 x x
       grind)
    | exact superpose eq411 eq488
    | exact resolve eq488 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq502 : ∀ X0 : G, (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq489 eq13
    | (have j0 := eq13 X0 (M.op x (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (M.op x (M.op x y))
       have r₂ := eq489 (M.op x (M.op x y))
       grind)
    | exact resolve eq13 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq502 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq515 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op x y) y) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq54 x x X2 X3 X5
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq516 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X2 X3 X5
    first
    | exact superpose eq214 eq515
    | exact resolve eq515 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq517 : ∀ X5 : G, (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | (have i₁ := eq516 x x X5
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq516
    | exact resolve eq516 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq518 : ∀ X5 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | exact superpose eq214 eq517
    | exact resolve eq517 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq553 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (k X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq55 X0 X0
       have i₂ := eq506 X0
       grind)
    | exact superpose eq506 eq55
    | exact resolve eq55 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (k X0 (M.op x (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq411 X0 X0
       have i₂ := eq506 X0
       grind)
    | exact superpose eq506 eq411
    | exact resolve eq411 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq558 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (k X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq214 eq553
    | exact resolve eq553 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq755 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq95 X0 X0
       grind)
    | exact superpose eq95 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq95 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq95 X1 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq95 X0 X1
       grind)
    | exact resolve eq13 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq759 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq755 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq764 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq759 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq759 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq759 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq3803 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq506 eq764
    | (have j0 := eq764 (M.op x (M.op x y)) X0
       grind)
    | exact resolve eq764 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq3819 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op x (M.op x y))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq489 eq3803
    | (have j0 := eq3803 X0
       grind)
    | exact resolve eq3803 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3803
  have eq3820 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have j0 := eq3819 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3819
  have eq3859 : ∀ X0 : G, (k (τ X0) (M.op x (M.op x y))) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq3820 eq259
    | exact resolve eq259 eq3820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq3865 : (M.op (σ y) (σ y)) = (σ (k y (M.op x (M.op x y)))) := by
    first
    | exact superpose eq3820 eq36
    | exact resolve eq36 eq3820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq3820
  have eq3889 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq506 eq3865
    | exact resolve eq3865 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3865
  have eq4047 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq3889
       grind)
    | exact superpose eq3889 eq16
    | exact resolve eq16 eq3889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3889
  have eq4198 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq194 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq194
    | (have j0 := eq194 y
       grind)
    | exact resolve eq194 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq4211 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq4198
  have eq4220 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4211
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq4211
    | exact resolve eq4211 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq4211
  have eq4246 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq4220
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq4220 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4220
  have eq4264 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq4246 eq89
    | exact resolve eq89 eq4246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq4246
  have eq4328 : (k y y) = (M.op y y) := by
    first
    | exact superpose eq4264 eq4047
    | exact resolve eq4047 eq4264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4047
  have eq4622 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq506 eq3859
    | exact resolve eq3859 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq4627 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq3859 eq558
    | exact resolve eq558 eq3859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq4628 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | exact superpose eq3859 eq554
    | exact resolve eq554 eq3859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554 eq3859
  have eq5609 : (M.op x (M.op x y)) = (M.op (τ (M.op x (M.op x y))) (τ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq518 eq4627
    | exact resolve eq4627 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4627
  have eq5640 : (M.op x (M.op x y)) = (τ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq5609
       have i₂ := eq4622 (M.op x sF0)
       grind)
    | exact superpose eq4622 eq5609
    | exact resolve eq5609 eq4622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5609
  have eq5679 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq518 eq5640
    | exact resolve eq5640 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5640
  have eq5715 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq5679 eq15
    | exact resolve eq15 eq5679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16591 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq16592 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq16591
    | exact resolve eq16591 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16591
  have eq16603 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq16592
       have r₂ := eq27
       grind)
    | exact resolve eq16592 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16592
  have eq16607 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq16603
    | exact resolve eq16603 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16603
  have eq16613 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq16607 eq4264
    | exact resolve eq4264 eq16607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4264 eq16607
  have eq16633 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16613
       have i₂ := eq4328
       grind)
    | exact superpose eq4328 eq16613
    | exact resolve eq16613 eq4328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4328 eq16613
  have eq16641 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq16633
    | exact resolve eq16633 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq16633
  have eq16642 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16641
  have eq16656 : (M.op y y) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq411 y y
       have i₂ := eq16642
       grind)
    | exact superpose eq16642 eq411
    | exact resolve eq411 eq16642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16869 : y = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16642
       have i₂ := eq16656
       grind)
    | exact superpose eq16656 eq16642
    | exact resolve eq16642 eq16656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16642 eq16656
  have eq16884 : y = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16869
  have eq16900 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16884 eq489
    | exact resolve eq489 eq16884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16915 : y = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16884 eq5715
    | exact resolve eq5715 eq16884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16920 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16884 eq55
    | exact resolve eq55 eq16884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq16884
  have eq16924 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq214 eq16920
    | exact resolve eq16920 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16920
  have eq16928 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16915
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16915
    | exact resolve eq16915 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16915
  have eq16931 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16924
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16924
    | exact resolve eq16924 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16924
  have eq16936 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16928 eq229
    | exact resolve eq229 eq16928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16939 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq16936
    | exact resolve eq16936 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16936
  have eq17349 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16900 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16900
    | (have j0 := eq16900 x
       grind)
    | exact resolve eq16900 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16900
  have eq17574 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17349 eq229
    | exact resolve eq229 eq17349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17578 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq17574
    | exact resolve eq17574 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17574
  have eq17644 : (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16931 eq5715
    | exact resolve eq5715 eq16931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5715 eq16931
  have eq17660 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq17644
    | exact resolve eq17644 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17644
  have eq17668 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17660 eq229
    | exact resolve eq229 eq17660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq17672 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq17668
    | exact resolve eq17668 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17668
  have eq17735 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ y = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16939 eq5679
    | exact resolve eq5679 eq16939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16939
  have eq17760 : (σ x) = (τ (σ x)) ∨ y = (σ y) ∨ x = (M.op x y) ∨ y = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16928 eq17735
    | exact resolve eq17735 eq16928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16928 eq17735
  have eq17793 : (σ x) = (τ (σ x)) ∨ y = (σ y) ∨ x = (M.op x y) := by grind
  clear eq17760
  have eq17797 : y = (σ y) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq17793
    | exact resolve eq17793 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17793
  have eq17800 : (M.op (σ x) (σ y)) = (M.op (σ x) y) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17797 eq26
    | exact resolve eq26 eq17797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18222 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17578 eq518
    | exact resolve eq518 eq17578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18234 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17578 eq5679
    | exact resolve eq5679 eq17578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5679 eq17578
  have eq18261 : (σ x) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17349 eq18234
    | exact resolve eq18234 eq17349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18234
  have eq18296 : (σ x) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq18261
  have eq18300 : y = (M.op x y) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq18296
    | exact resolve eq18296 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq18296
  have eq18303 : (σ y) = (σ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18300 eq20
    | exact resolve eq20 eq18300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18358 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18300 eq489
    | exact resolve eq489 eq18300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18385 : x ≠ y ∨ x = (σ x) ∨ x = (M.op x y) := by grind
  have eq18403 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18358 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18358
    | (have j0 := eq18358 X0
       grind)
    | exact resolve eq18358 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18358
  have eq18458 : (σ (M.op x y)) = (σ y) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18303
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18303
    | exact resolve eq18303 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18303
  have eq18566 : y = (σ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18458 eq17797
    | exact resolve eq17797 eq18458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17797 eq18458
  have eq18567 : y = (σ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by grind
  clear eq18566
  have eq19022 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17672 eq518
    | exact resolve eq518 eq17672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518 eq17672
  have eq19523 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17349 eq18222
    | exact resolve eq18222 eq17349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17349 eq18222
  have eq19569 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq19523 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19523
  have eq19675 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17660 eq19022
    | exact resolve eq19022 eq17660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17660 eq19022
  have eq19723 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq19675 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19675
  have eq21156 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (σ x) ∨ x = y ∨ x = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18300 eq18403
    | exact resolve eq18403 eq18300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18300 eq18403
  have eq21252 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21156 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21156
  have eq21273 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21252 X0
       grind)
    | (have r₁ := eq21252 X0
       have r₂ := eq18385
       grind)
    | exact resolve eq21252 eq18385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18385 eq21252
  have eq24212 : y = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17800
       have i₂ := eq21273 sF2
       grind)
    | exact superpose eq21273 eq17800
    | exact resolve eq17800 eq21273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17800 eq21273
  have eq24225 : y = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by grind
  clear eq24212
  have eq24265 : y ≠ (σ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24225 eq27
    | exact resolve eq27 eq24225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24225
  have eq24313 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq24265
       have r₂ := eq18567
       grind)
    | exact resolve eq24265 eq18567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18567 eq24265
  have eq24391 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq24313 eq19569
    | exact resolve eq19569 eq24313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19569
  have eq24394 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq24313 eq19723
    | exact resolve eq19723 eq24313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19723 eq24313
  have eq24395 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq24394 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24394
  have eq24398 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq24391 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24391
  have eq25974 : x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq24395 y
       grind)
    | exact superpose eq24395 eq18
    | (have j1 := eq24395 y
       grind)
    | exact resolve eq18 eq24395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24395
  have eq26054 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq25974
  have eq26432 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq24398 y
       grind)
    | exact superpose eq24398 eq18
    | (have j1 := eq24398 y
       grind)
    | exact resolve eq18 eq24398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24398
  have eq26512 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq26432
  have eq26557 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26512 eq20
    | exact resolve eq20 eq26512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26612 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26512 eq489
    | exact resolve eq489 eq26512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489 eq26512
  have eq26694 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq26612 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq26612
    | (have j0 := eq26612 X0
       grind)
    | exact resolve eq26612 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26612
  have eq26749 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26557
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq26557
    | exact resolve eq26557 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq26557
  have eq26794 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26749 eq26
    | exact resolve eq26 eq26749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26749
  have eq27248 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26054 eq26794
    | exact resolve eq26794 eq26054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26794
  have eq27272 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq27248
  have eq27629 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27272 eq26694
    | exact resolve eq26694 eq27272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26694 eq27272
  have eq27641 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq27629
  have eq27943 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27641 eq27
    | exact resolve eq27 eq27641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27641
  have eq27995 : x = (M.op x y) := by
    first
    | (have r₁ := eq27943
       have r₂ := eq26054
       grind)
    | exact resolve eq27943 eq26054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26054 eq27943
  have eq27998 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq27995 eq20
    | exact resolve eq20 eq27995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq28044 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq27995 eq214
    | exact resolve eq214 eq27995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq28104 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq28044
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28044
    | exact resolve eq28044 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq28044
  have eq28149 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq27998
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27998
    | exact resolve eq27998 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27998
  have eq28154 : x = (M.op x x) := by
    first
    | exact superpose eq27995 eq28104
    | exact resolve eq28104 eq27995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28104
  have eq28192 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq28149 eq26
    | exact resolve eq26 eq28149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq28891 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq28154
       grind)
    | exact superpose eq28154 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq28154
       grind)
    | exact resolve eq13 eq28154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28893 : (M.op x (M.op x y)) = (M.op (τ x) (τ x)) := by
    first
    | (have i₁ := eq4628 x
       have i₂ := eq28154
       grind)
    | exact superpose eq28154 eq4628
    | exact resolve eq4628 eq28154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4628
  have eq28901 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq28891 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28891
  have eq28908 : (M.op x (M.op x y)) = (τ (M.op x x)) := by
    first
    | (have i₁ := eq28893
       have i₂ := eq4622 x
       grind)
    | exact superpose eq4622 eq28893
    | exact resolve eq28893 eq4622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4622 eq28893
  have eq28919 : (M.op x (M.op x y)) = (τ x) := by
    first
    | (have i₁ := eq28908
       have i₂ := eq28154
       grind)
    | exact superpose eq28154 eq28908
    | exact resolve eq28908 eq28154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28908
  have eq28930 : (M.op x x) = (τ x) := by
    first
    | exact superpose eq27995 eq28919
    | exact resolve eq28919 eq27995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28919
  have eq28938 : x = (τ x) := by
    first
    | (have i₁ := eq28930
       have i₂ := eq28154
       grind)
    | exact superpose eq28154 eq28930
    | exact resolve eq28930 eq28154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28930
  have eq28942 : x = (σ x) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq28938
       grind)
    | exact superpose eq28938 eq15
    | exact resolve eq15 eq28938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28938
  have eq29030 : x = (σ x) := by
    first
    | (have i₁ := eq28942
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28942
    | exact resolve eq28942 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq28942
  have eq29051 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq28149 eq29030
    | exact resolve eq29030 eq28149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28149 eq29030
  have eq29455 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq29051 eq28192
    | exact resolve eq28192 eq29051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28192
  have eq33029 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (k X0 x) X0) := by
    intro X0
    first
    | (have i₁ := eq411 X0 X0
       have i₂ := eq28901 X0
       grind)
    | exact superpose eq28901 eq411
    | exact resolve eq411 eq28901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28901
  have eq33115 : ∀ X0 : G, (M.op x x) = (M.op (k X0 x) X0) := by
    intro X0
    first
    | exact superpose eq27995 eq33029
    | exact resolve eq33029 eq27995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33029
  have eq33175 : ∀ X0 : G, x = (M.op (k X0 x) X0) := by
    intro X0
    first
    | (have i₁ := eq33115 X0
       have i₂ := eq28154
       grind)
    | exact superpose eq28154 eq33115
    | exact resolve eq33115 eq28154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33115
  have eq34302 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq411 (k X0 x) X0
       have i₂ := eq33175 X0
       grind)
    | exact superpose eq33175 eq411
    | exact resolve eq411 eq33175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411 eq33175
  have eq34327 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq27995 eq34302
    | exact resolve eq34302 eq27995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27995 eq34302
  have eq34341 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq34327 X0
       have i₂ := eq28154
       grind)
    | exact superpose eq28154 eq34327
    | exact resolve eq34327 eq28154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28154 eq34327
  have eq34372 : x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29455 eq34341
    | exact resolve eq34341 eq29455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29455 eq34341
  have eq34531 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq34372 eq27
    | exact resolve eq27 eq34372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq34372
  have eq34565 : False := by grind
  exact eq34565

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_y_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq20 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
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
  have eq29 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    grind
  have eq32 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
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
  have eq37 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq29 X0
       have i₂ := eq21 (τ X0)
       grind)
    | exact superpose eq21 eq29
    | exact resolve eq29 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq38 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq40 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
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
  have eq42 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq46 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq42
    | exact resolve eq42 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq77 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq84 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq20 X1 X0 X3
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq75 (k (τ X0) X1) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq75
    | exact resolve eq75 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ X2) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq75 X0 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq75
    | exact resolve eq75 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq75 x y
       grind)
    | exact superpose eq75 eq16
    | (have j1 := eq75 x y
       grind)
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq190 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (M.op (σ X0) X1) (σ X2)) ∨ (M.op (σ X0) X1) = X1 ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 X0 X1 X2
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq33
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq33 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq227 : ∀ X0 : G, (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) = (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq27 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0
       have i₂ := eq37 (σ X0)
       grind)
    | exact superpose eq37 eq27
    | exact resolve eq27 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ X0))) = (k (M.op (τ (σ X0)) (τ (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq227 X0
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq227
    | exact resolve eq227 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq244 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq229 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq229
    | exact resolve eq229 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq371 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq77 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq77
    | exact resolve eq77 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq77 X0 (τ X0)
       grind)
    | exact superpose eq77 eq37
    | (have j1 := eq77 X0 (τ X0)
       grind)
    | exact resolve eq37 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq394 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq376 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq400 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq394 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq394
    | (have j0 := eq394 X0
       grind)
    | exact resolve eq394 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq404 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq371 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq371
    | (have j0 := eq371 X0 X1
       grind)
    | exact resolve eq371 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq697 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq119 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq119
    | (have j0 := eq119 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq119 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq700 : ∀ X0 X1 : G, (σ (σ X1)) ≠ (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq119 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq119
    | (have j0 := eq119 (σ X0) (σ X1)
       grind)
    | exact resolve eq119 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq704 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq119 (τ X0) (τ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq119
    | (have j0 := eq119 (τ X0) (τ X1)
       grind)
    | exact resolve eq119 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq712 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq704 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq704
    | (have j0 := eq704 X0 X1
       grind)
    | exact resolve eq704 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq716 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq712 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq712
    | (have j0 := eq712 X0 X1
       grind)
    | exact resolve eq712 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq718 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq716 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq716
    | (have j0 := eq716 X0 X1
       grind)
    | exact resolve eq716 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq719 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq718 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq718
    | (have j0 := eq718 X0 X1
       grind)
    | exact resolve eq718 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq720 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq719 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq719
    | (have j0 := eq719 X0 X1
       grind)
    | exact resolve eq719 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq721 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq720 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq720
    | (have j0 := eq720 X0 X1
       grind)
    | exact resolve eq720 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq835 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq400 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq400
    | (have j0 := eq400 (σ X0)
       grind)
    | exact resolve eq400 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq873 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq835 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq835
    | (have j0 := eq835 X0
       grind)
    | exact resolve eq835 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq888 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq873 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq873
    | (have j0 := eq873 X0
       grind)
    | exact resolve eq873 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq1004 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq84 x X2 X0 X1
       grind)
    | exact superpose eq84 eq9
    | exact resolve eq9 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq1031 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq1004 x X1 X0
       grind)
    | exact superpose eq1004 eq9
    | exact resolve eq9 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1035 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X2 X0
       have i₂ := eq1004 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq1004 eq9
    | exact resolve eq9 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1071 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq112
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq112
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq112 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq1072 : y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq1071
  have eq1075 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    grind
  have eq1100 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) X0) ∨ (σ (k (τ X0) (τ X0))) = (σ (k (k (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq888 (τ X0)
       grind)
    | exact superpose eq888 eq37
    | (have j1 := eq888 (τ X0)
       grind)
    | exact resolve eq37 eq888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq1102 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ (k (τ X0) (τ X0))) = (σ (k (k (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1100 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1100
    | (have j0 := eq1100 X0
       grind)
    | exact resolve eq1100 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100
  have eq1106 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1102 X0
       have i₂ := eq19 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq19 eq1102
    | (have j0 := eq1102 X0
       grind)
    | exact resolve eq1102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq1109 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1106 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq1106
    | (have j0 := eq1106 X0
       grind)
    | exact resolve eq1106 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106
  have eq1112 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1109 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1109
    | (have j0 := eq1109 X0
       grind)
    | exact resolve eq1109 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109
  have eq1115 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1112 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq1112
    | exact resolve eq1112 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112
  have eq1153 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq1115 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq1115
    | (have j0 := eq1115 X0
       grind)
    | exact resolve eq1115 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115
  have eq1603 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (k X1 (σ X2)) (σ X0)) ∨ (k X1 (σ X2)) = (M.op (σ X0) (σ X0)) ∨ (M.op (k X1 (σ X2)) (σ X0)) = (σ (k (k (τ X1) X2) X0)) ∨ (k X1 (σ X2)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k X1 (σ X2)) (σ X0)
       have i₂ := eq107 X1 X2 X0
       grind)
    | exact superpose eq107 eq13
    | (have j0 := eq13 (k X1 (σ X2)) (σ X0)
       have j1 := eq107 X1 X2 X0
       grind)
    | (have r₁ := eq13 (k X0 (σ X1)) (σ X2)
       have r₂ := eq107 X0 X1 X2
       grind)
    | exact resolve eq13 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1604 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (k X1 (σ X2)) (σ X0)) ∨ (k X1 (σ X2)) = (M.op (σ X0) (σ X0)) ∨ (M.op (k X1 (σ X2)) (σ X0)) = (σ (k (k (τ X1) X2) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1603 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1603
  have eq1605 : ∀ X0 X1 X2 : G, (σ X0) = (k (k X1 (σ X2)) (σ X0)) ∨ (k X1 (σ X2)) = (M.op (σ X0) (σ X0)) ∨ (M.op (k X1 (σ X2)) (σ X0)) = (σ (k (k (τ X1) X2) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1604 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1604
  have eq1606 : ∀ X0 X1 X2 : G, (σ X0) = (σ (k (k (τ X1) X2) X0)) ∨ (k X1 (σ X2)) = (M.op (σ X0) (σ X0)) ∨ (M.op (k X1 (σ X2)) (σ X0)) = (σ (k (k (τ X1) X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1605 X0 X1 X2
       have i₂ := eq26 X1 X2 X0
       grind)
    | exact superpose eq26 eq1605
    | (have j0 := eq1605 X0 X1 X2
       grind)
    | exact resolve eq1605 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1605
  have eq1887 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (σ (τ (k X0 X0))) = (σ (k (τ (k X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1075 (τ X0)
       have i₂ := eq38 X0 X0
       grind)
    | exact superpose eq38 eq1075
    | exact resolve eq1075 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075
  have eq1952 : ∀ X0 : G, (σ (τ (k X0 X0))) = (k (σ (τ (k X0 X0))) X0) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1887 X0
       have i₂ := eq19 X0 (τ (k X0 X0))
       grind)
    | exact superpose eq19 eq1887
    | (have j0 := eq1887 X0
       grind)
    | exact resolve eq1887 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1887
  have eq1970 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1952 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq1952
    | (have j0 := eq1952 X0
       grind)
    | exact resolve eq1952 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1952
  have eq2345 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (k (σ X0) X1) ∨ (k (σ X0) X1) = (k (σ X2) (k (σ X0) X1)) ∨ (σ X2) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ X2) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (σ X2) (k (σ X0) X1)
       have i₂ := eq111 X0 X1 X2
       grind)
    | exact superpose eq111 eq13
    | (have j0 := eq13 (σ X2) (k (σ X0) X1)
       have j1 := eq111 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X2) (k (σ X0) X1)
       have r₂ := eq111 X0 X1 X2
       grind)
    | exact resolve eq13 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2346 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (k (σ X0) X1) ∨ (k (σ X0) X1) = (k (σ X2) (k (σ X0) X1)) ∨ (σ X2) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2345 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2345
  have eq2347 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (k (σ X2) (k (σ X0) X1)) ∨ (σ X2) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2346 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2346
  have eq2348 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (k X2 (k X0 (τ X1)))) ∨ (σ X2) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2347 X0 X1 X2
       have i₂ := eq32 X0 X1 X2
       grind)
    | exact superpose eq32 eq2347
    | (have j0 := eq2347 X0 X1 X2
       grind)
    | exact resolve eq2347 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq2347
  have eq2730 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k (k X0 X0) X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1153 x
       have i₂ := eq404 x x
       grind)
    | exact superpose eq404 eq1153
    | (have j1 := eq404 X0 X0
       grind)
    | exact resolve eq1153 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404 eq1153
  have eq2778 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k (k X0 X0) X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2730 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2730
  have eq3651 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1004 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) X1 X2
       have i₂ := eq1035 (M.op X1 X2) X0 (M.op X1 X2)
       grind)
    | exact superpose eq1035 eq1004
    | exact resolve eq1004 eq1035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035
  have eq3713 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 (M.op X0 (M.op X1 X2)) X2 X2
       have i₂ := eq3651 X0 X1 X2
       grind)
    | exact superpose eq3651 eq20
    | exact resolve eq20 eq3651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3651
  have eq7028 : ∀ X0 : G, (σ (τ (k X0 X0))) = (k (σ (τ (k X0 X0))) X0) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq1970 X0
       grind)
    | exact superpose eq1970 eq37
    | (have j1 := eq1970 X0
       grind)
    | exact resolve eq37 eq1970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1970
  have eq7066 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq7028 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq7028
    | (have j0 := eq7028 X0
       grind)
    | exact resolve eq7028 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7028
  have eq7067 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq7066 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7066
  have eq11836 : y ≠ y ∨ y = (k x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1072
       grind)
    | exact superpose eq1072 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1072
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1072
       grind)
    | exact resolve eq13 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq11858 : y ≠ y ∨ y = (k x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11836
  have eq11859 : y = (k x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11858
  have eq12775 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 (τ (σ X0))) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq244 (σ X0)
       have i₂ := eq190 X0 (σ X0) X0
       grind)
    | exact superpose eq190 eq244
    | (have j1 := eq190 X0 (σ X0) x
       grind)
    | exact resolve eq244 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq244
  have eq12790 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 (τ (σ X0))) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq12775 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12775
  have eq12801 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq12790 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12790
    | (have j0 := eq12790 X0
       grind)
    | exact resolve eq12790 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12790
  have eq12855 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12801 X0
       have i₂ := eq7067 X0
       grind)
    | exact superpose eq7067 eq12801
    | (have j0 := eq12801 X0
       grind)
    | exact resolve eq12801 eq7067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12801
  have eq12903 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  clear eq12855
  have eq12936 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12903 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq12903
    | (have j0 := eq12903 X0
       grind)
    | exact resolve eq12903 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12903
  have eq12937 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq12936 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12936
  have eq12964 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq12937 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12937
    | exact resolve eq12937 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13024 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1031 (σ X0) (σ X0)
       have i₂ := eq12937 X0
       grind)
    | exact superpose eq12937 eq1031
    | exact resolve eq1031 eq12937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13028 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op X1 (M.op X2 (σ (k X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3713 (σ X0) X2 (σ X0) X1
       have i₂ := eq12937 X0
       grind)
    | exact superpose eq12937 eq3713
    | exact resolve eq3713 eq12937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13062 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq12964 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq12964
    | exact resolve eq12964 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12964
  have eq13070 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq13062 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13062
    | exact resolve eq13062 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13062
  have eq14425 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13024 X0
       have i₂ := eq13070 X0
       grind)
    | exact superpose eq13070 eq13024
    | exact resolve eq13024 eq13070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13024
  have eq15618 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op X1 (σ (M.op (k X0 X0) (k X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq13028 X0 X1 (σ (M.op (k X0 X0) (k X0 X0)))
       have i₂ := eq14425 (k X0 X0)
       grind)
    | exact superpose eq14425 eq13028
    | exact resolve eq13028 eq14425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13028
  have eq15724 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op X1 (σ (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq15618 X0 X1
       have i₂ := eq13070 X0
       grind)
    | exact superpose eq13070 eq15618
    | exact resolve eq15618 eq13070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15618
  have eq17285 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3713 (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0) x X1
       have i₂ := eq15724 X0 x
       grind)
    | exact superpose eq15724 eq3713
    | exact resolve eq3713 eq15724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15724
  have eq28617 : ∀ X0 X1 : G, (σ (σ (τ X1))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq700 (τ X0) (τ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq700
    | (have j0 := eq700 (τ X0) (τ X1)
       grind)
    | exact resolve eq700 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq700
  have eq28732 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X1))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28617 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq28617
    | (have j0 := eq28617 X0 X1
       grind)
    | exact resolve eq28617 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28617
  have eq28800 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28732 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq28732
    | (have j0 := eq28732 X0 X1
       grind)
    | exact resolve eq28732 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28732
  have eq28865 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (σ (τ X0))) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28800 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28800
    | (have j0 := eq28800 X0 X1
       grind)
    | exact resolve eq28800 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28800
  have eq28914 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28865 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28865
    | (have j0 := eq28865 X0 X1
       grind)
    | exact resolve eq28865 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28865
  have eq28955 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) (σ (τ X1)))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28914 X0 X1
       have i₂ := eq12937 (σ (τ X1))
       grind)
    | exact superpose eq12937 eq28914
    | (have j0 := eq28914 X0 X1
       grind)
    | exact resolve eq28914 eq12937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28914
  have eq28991 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (σ (k (τ X1) (τ X1)))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28955 X0 X1
       have i₂ := eq15 (τ X1) (τ X1)
       grind)
    | exact superpose eq15 eq28955
    | (have j0 := eq28955 X0 X1
       grind)
    | exact resolve eq28955 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28955
  have eq29025 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28991 X0 X1
       have i₂ := eq19 X1 (τ X1)
       grind)
    | exact superpose eq19 eq28991
    | (have j0 := eq28991 X0 X1
       grind)
    | exact resolve eq28991 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28991
  have eq29052 : ∀ X0 X1 : G, (σ (k X1 X1)) = (σ (σ (τ X0))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29025 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq29025
    | (have j0 := eq29025 X0 X1
       grind)
    | exact resolve eq29025 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29025
  have eq29074 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29052 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29052
    | (have j0 := eq29052 X0 X1
       grind)
    | exact resolve eq29052 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29052
  have eq29093 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29074 X0 X1
       have i₂ := eq13070 X1
       grind)
    | exact superpose eq13070 eq29074
    | (have j0 := eq29074 X0 X1
       grind)
    | exact resolve eq29074 eq13070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29074
  have eq56639 : ∀ X0 X1 X2 : G, (σ X2) ≠ (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1606 X2 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1606
  have eq56648 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq56639 X0 X1 X2
       have j1 := eq107 X0 X1 X2
       grind)
    | (have r₁ := eq56639 X0 X1 X2
       have r₂ := eq107 X0 X1 X2
       grind)
    | exact resolve eq56639 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq56639
  have eq56836 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (k X2 X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56648 X0 X1 X2
       have i₂ := eq12937 X2
       grind)
    | exact superpose eq12937 eq56648
    | (have j0 := eq56648 X0 X1 X2
       grind)
    | exact resolve eq56648 eq12937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56648
  have eq57023 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56836 X0 X1 X2
       have i₂ := eq13070 X2
       grind)
    | exact superpose eq13070 eq56836
    | (have j0 := eq56836 X0 X1 X2
       grind)
    | exact resolve eq56836 eq13070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56836
  have eq85307 : ∀ X0 X1 X2 : G, (k (σ X1) X2) ≠ (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (M.op (k (σ X1) X2) (k (σ X1) X2)) ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2348 X1 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2348
  have eq85308 : ∀ X0 X1 X2 : G, (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (M.op (k (σ X1) X2) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq85307 X0 X1 X2
       have j1 := eq111 X1 X2 X0
       grind)
    | (have r₁ := eq85307 X2 X0 X1
       have r₂ := eq111 X0 X1 X2
       grind)
    | exact resolve eq85307 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq85307
  have eq259170 : ∀ X0 X1 : G, (σ (k (τ (M.op (σ X0) (σ X0))) X1)) = (M.op (k (M.op (σ X0) (σ X0)) (σ X0)) (σ X1)) ∨ (k (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq57023 (M.op (σ X0) (σ X0)) X0 X1
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq57023
    | (have j0 := eq57023 (M.op (σ X0) (σ X0)) X0 X1
       grind)
    | exact resolve eq57023 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq57023
  have eq259848 : ∀ X0 X1 : G, (σ (k (τ (M.op (σ X0) (σ X0))) X1)) = (M.op (M.op (M.op (σ X0) (σ X0)) (σ X0)) (σ X1)) ∨ (k (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    grind
  clear eq259170
  have eq260085 : ∀ X0 X1 : G, (σ (k (τ (M.op (σ X0) (σ X0))) X1)) = (M.op (M.op (σ X0) (σ X0)) (σ X1)) ∨ (k (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq259848 X0 X1
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq259848
    | (have j0 := eq259848 X0 X1
       grind)
    | exact resolve eq259848 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259848
  have eq260280 : ∀ X0 X1 : G, (M.op (σ (k X0 X0)) (σ X1)) = (σ (k (τ (σ (k X0 X0))) X1)) ∨ (k (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq260085 X0 X1
       have i₂ := eq12937 X0
       grind)
    | exact superpose eq12937 eq260085
    | (have j0 := eq260085 X0 X1
       grind)
    | exact resolve eq260085 eq12937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260085
  have eq260440 : ∀ X0 X1 : G, (M.op (σ (k X0 X0)) (σ X1)) = (k (σ (k X0 X0)) (σ X1)) ∨ (k (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq260280 X0 X1
       have i₂ := eq18 (σ (k X0 X0)) X1
       grind)
    | exact superpose eq18 eq260280
    | (have j0 := eq260280 X0 X1
       grind)
    | exact resolve eq260280 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260280
  have eq260556 : ∀ X0 X1 : G, (σ (k (k X0 X0) X1)) = (M.op (σ (k X0 X0)) (σ X1)) ∨ (k (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq260440 X0 X1
       have i₂ := eq15 (k X0 X0) X1
       grind)
    | exact superpose eq15 eq260440
    | (have j0 := eq260440 X0 X1
       grind)
    | exact resolve eq260440 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260440
  have eq260587 : ∀ X0 X1 : G, (σ (k (M.op X0 X0) X1)) = (M.op (σ (M.op X0 X0)) (σ X1)) ∨ (k (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq260556 X0 X1
       have i₂ := eq13070 X0
       grind)
    | exact superpose eq13070 eq260556
    | (have j0 := eq260556 X0 X1
       grind)
    | exact resolve eq260556 eq13070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260556
  have eq260603 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k (M.op X0 X0) X1)) = (M.op (σ (M.op X0 X0)) (σ X1)) := by
    intro X0 X1
    grind
  clear eq260587
  have eq260614 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k (M.op X0 X0) X1)) = (M.op (σ (M.op X0 X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq260603 X0 X1
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq260603
    | (have j0 := eq260603 X0 X1
       grind)
    | exact resolve eq260603 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq260603
  have eq260623 : ∀ X0 X1 : G, (σ (k X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k (M.op X0 X0) X1)) = (M.op (σ (M.op X0 X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq260614 X0 X1
       have i₂ := eq12937 X0
       grind)
    | exact superpose eq12937 eq260614
    | (have j0 := eq260614 X0 X1
       grind)
    | exact resolve eq260614 eq12937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260614
  have eq260628 : ∀ X0 X1 : G, (σ (k (M.op X0 X0) X1)) = (M.op (σ (M.op X0 X0)) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq260623 X0 X1
       have i₂ := eq13070 X0
       grind)
    | exact superpose eq13070 eq260623
    | (have j0 := eq260623 X0 X1
       grind)
    | exact resolve eq260623 eq13070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260623
  have eq555717 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29093 x y
       have i₂ := eq11859
       grind)
    | exact superpose eq11859 eq29093
    | (have j0 := eq29093 x y
       grind)
    | exact resolve eq29093 eq11859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11859 eq29093
  have eq555773 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq555717
  have eq555774 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq555773
  have eq555832 : (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq555774
       have i₂ := eq12937 y
       grind)
    | exact superpose eq12937 eq555774
    | exact resolve eq555774 eq12937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555774
  have eq555875 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq555832
       have i₂ := eq13070 y
       grind)
    | exact superpose eq13070 eq555832
    | exact resolve eq555832 eq13070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555832
  have eq555876 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq555875
  have eq560585 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq555876
       grind)
    | exact superpose eq555876 eq16
    | exact resolve eq16 eq555876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560621 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1031 (σ y) (σ x)
       have i₂ := eq555876
       grind)
    | exact superpose eq555876 eq1031
    | exact resolve eq1031 eq555876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560676 : (σ y) = (σ (k y y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq560621
       have i₂ := eq12937 y
       grind)
    | exact superpose eq12937 eq560621
    | exact resolve eq560621 eq12937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560621
  have eq560702 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq560676
       have i₂ := eq13070 y
       grind)
    | exact superpose eq13070 eq560676
    | exact resolve eq560676 eq13070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560676
  have eq563172 : (σ x) = (σ y) ∨ (σ x) = (σ (k (k y y) y)) ∨ x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2778 y
       have i₂ := eq560702
       grind)
    | exact superpose eq560702 eq2778
    | (have j0 := eq2778 y
       grind)
    | exact resolve eq2778 eq560702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2778
  have eq563300 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq697 y y
       have i₂ := eq560702
       grind)
    | exact superpose eq560702 eq697
    | (have j0 := eq697 y y
       grind)
    | (have r₁ := eq697 y y
       have r₂ := eq560702
       grind)
    | exact resolve eq697 eq560702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697 eq560702
  have eq563351 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq563300
  have eq563356 : (σ y) = (σ (k y y)) ∨ (σ x) ≠ (σ y) ∨ x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq563351
       have i₂ := eq12937 y
       grind)
    | exact superpose eq12937 eq563351
    | exact resolve eq563351 eq12937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563351
  have eq563365 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq563172
       have i₂ := eq7067 y
       grind)
    | exact superpose eq7067 eq563172
    | exact resolve eq563172 eq7067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7067 eq563172
  have eq563372 : (σ y) = (σ (M.op y y)) ∨ (σ x) ≠ (σ y) ∨ x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq563356
       have i₂ := eq13070 y
       grind)
    | exact superpose eq13070 eq563356
    | exact resolve eq563356 eq13070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563356
  have eq563373 : (σ y) = (σ (M.op y y)) ∨ (σ x) ≠ (σ y) ∨ x = y ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq563372
  have eq563376 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq563365
       have i₂ := eq13070 y
       grind)
    | exact superpose eq13070 eq563365
    | exact resolve eq563365 eq13070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563365
  have eq563377 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq563376
  have eq563383 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq563377
       have r₂ := eq563373
       grind)
    | exact resolve eq563377 eq563373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563373 eq563377
  have eq566109 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq563383
       grind)
    | exact superpose eq563383 eq16
    | exact resolve eq16 eq563383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563383
  have eq566126 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq566109
       have i₂ := eq12937 x
       grind)
    | exact superpose eq12937 eq566109
    | exact resolve eq566109 eq12937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566109
  have eq566131 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq566126
       have i₂ := eq13070 x
       grind)
    | exact superpose eq13070 eq566126
    | exact resolve eq566126 eq13070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566126
  have eq566132 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq566131
  have eq566179 : ∀ X0 : G, (k (τ X0) (M.op y y)) = (τ (k X0 (σ y))) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq27 X0 (M.op y y)
       have i₂ := eq566132
       grind)
    | exact superpose eq566132 eq27
    | exact resolve eq27 eq566132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq566184 : ∀ X0 : G, (k (M.op y y) (τ X0)) = (τ (k (σ y) X0)) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq34 (M.op y y) X0
       have i₂ := eq566132
       grind)
    | exact superpose eq566132 eq34
    | exact resolve eq34 eq566132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq566488 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq566132
  have eq566661 : ∀ X0 : G, (k y (τ X0)) = (k (M.op y y) (τ X0)) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq566184 X0
       have i₂ := eq34 y X0
       grind)
    | exact superpose eq34 eq566184
    | exact resolve eq566184 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq566184
  have eq566666 : ∀ X0 : G, (k (τ X0) y) = (k (τ X0) (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq566179 X0
       have i₂ := eq27 X0 y
       grind)
    | exact superpose eq27 eq566179
    | exact resolve eq566179 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566179
  have eq577107 : ∀ X0 : G, (σ x) = (σ (M.op y y)) ∨ (k y X0) = (k (M.op y y) X0) := by
    intro X0
    first
    | (have i₁ := eq566661 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq566661
    | exact resolve eq566661 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566661
  have eq578782 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (k y X0) = (k (M.op y y) X0) := by
    intro X0
    first
    | (have i₁ := eq14425 y
       have i₂ := eq577107 X0
       grind)
    | exact superpose eq577107 eq14425
    | (have j1 := eq577107 X0
       grind)
    | exact resolve eq14425 eq577107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq578815 : ∀ X0 : G, (M.op y y) = (τ (σ x)) ∨ (k y X0) = (k (M.op y y) X0) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq577107 X0
       grind)
    | exact superpose eq577107 eq10
    | (have j1 := eq577107 X0
       grind)
    | exact resolve eq10 eq577107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577107
  have eq579313 : ∀ X0 : G, x = (M.op y y) ∨ (k y X0) = (k (M.op y y) X0) := by
    intro X0
    first
    | (have i₁ := eq578815 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq578815
    | (have j0 := eq578815 X0
       grind)
    | exact resolve eq578815 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578815
  have eq579786 : ∀ X0 : G, x = (M.op x y) ∨ (k y X0) = (k (M.op y y) X0) := by
    intro X0
    first
    | (have i₁ := eq1031 y y
       have i₂ := eq579313 X0
       grind)
    | exact superpose eq579313 eq1031
    | (have j1 := eq579313 X0
       grind)
    | exact resolve eq1031 eq579313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579313
  have eq582131 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (k y X0) = (k (M.op y y) X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq578782 X0
       grind)
    | exact superpose eq578782 eq16
    | (have j1 := eq578782 X0
       grind)
    | exact resolve eq16 eq578782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578782
  have eq585616 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (k y X0) = (k (M.op y y) X0) ∨ (k y X1) = (k (M.op y y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq582131 X0
       have i₂ := eq579786 X1
       grind)
    | exact superpose eq579786 eq582131
    | (have j0 := eq582131 X0
       have j1 := eq579786 X0
       grind)
    | exact resolve eq582131 eq579786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579786 eq582131
  have eq585618 : ∀ X0 X1 : G, (k y X0) = (k (M.op y y) X0) ∨ (k y X1) = (k (M.op y y) X1) := by
    intro X0 X1
    first
    | (have j0 := eq585616 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585616
  have eq588871 : ∀ X0 : G, (σ x) = (σ (M.op y y)) ∨ (k X0 y) = (k X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq566666 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq566666
    | exact resolve eq566666 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566666
  have eq589163 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 y) = (k X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq14425 y
       have i₂ := eq588871 X0
       grind)
    | exact superpose eq588871 eq14425
    | (have j1 := eq588871 X0
       grind)
    | exact resolve eq14425 eq588871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14425
  have eq589196 : ∀ X0 : G, (M.op y y) = (τ (σ x)) ∨ (k X0 y) = (k X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq588871 X0
       grind)
    | exact superpose eq588871 eq10
    | (have j1 := eq588871 X0
       grind)
    | exact resolve eq10 eq588871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588871
  have eq589703 : ∀ X0 : G, x = (M.op y y) ∨ (k X0 y) = (k X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq589196 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq589196
    | (have j0 := eq589196 X0
       grind)
    | exact resolve eq589196 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589196
  have eq592209 : ∀ X0 : G, x = (M.op x y) ∨ (k X0 y) = (k X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq1031 y y
       have i₂ := eq589703 X0
       grind)
    | exact superpose eq589703 eq1031
    | (have j1 := eq589703 X0
       grind)
    | exact resolve eq1031 eq589703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031 eq589703
  have eq596281 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (k X0 y) = (k X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq589163 X0
       grind)
    | exact superpose eq589163 eq16
    | (have j1 := eq589163 X0
       grind)
    | exact resolve eq16 eq589163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589163
  have eq596548 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (k X0 y) = (k X0 (M.op y y)) ∨ (k X1 y) = (k X1 (M.op y y)) := by
    intro X0 X1
    first
    | (have i₁ := eq596281 X0
       have i₂ := eq592209 X1
       grind)
    | exact superpose eq592209 eq596281
    | (have j0 := eq596281 X0
       have j1 := eq592209 X0
       grind)
    | exact resolve eq596281 eq592209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592209 eq596281
  have eq596552 : ∀ X0 X1 : G, (k X0 y) = (k X0 (M.op y y)) ∨ (k X1 y) = (k X1 (M.op y y)) := by
    intro X0 X1
    first
    | (have j0 := eq596548 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596548
  have eq655395 : ∀ X0 : G, (k y X0) ≠ (k y X0) ∨ (k y X0) = (k (M.op y y) X0) := by
    intro X0
    first
    | (have j0 := eq585618 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585618
  have eq655396 : ∀ X0 : G, (k y X0) = (k (M.op y y) X0) := by
    intro X0
    first
    | (have j0 := eq655395 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655395
  have eq655693 : (M.op (M.op y y) (M.op y y)) = (k y (M.op y y)) := by
    first
    | (have i₁ := eq13070 (M.op y y)
       have i₂ := eq655396 (M.op y y)
       grind)
    | exact superpose eq655396 eq13070
    | exact resolve eq13070 eq655396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655396
  have eq665590 : ∀ X0 : G, y = (M.op y (M.op X0 (k y (M.op y y)))) := by
    intro X0
    first
    | (have i₁ := eq3713 y (M.op y y) y X0
       have i₂ := eq655693
       grind)
    | exact superpose eq655693 eq3713
    | exact resolve eq3713 eq655693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3713 eq655693
  have eq733924 : ∀ X0 : G, (k X0 y) ≠ (k X0 y) ∨ (k X0 y) = (k X0 (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq596552 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596552
  have eq733925 : ∀ X0 : G, (k X0 y) = (k X0 (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq733924 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733924
  have eq737220 : ∀ X0 : G, y = (M.op y (M.op X0 (k y y))) := by
    intro X0
    first
    | (have i₁ := eq665590 X0
       have i₂ := eq733925 y
       grind)
    | exact superpose eq733925 eq665590
    | exact resolve eq665590 eq733925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665590 eq733925
  have eq737229 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq737220 X0
       have i₂ := eq13070 y
       grind)
    | exact superpose eq13070 eq737220
    | exact resolve eq737220 eq13070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737220
  have eq739118 : y = (M.op y y) := by
    first
    | (have i₁ := eq1004 y y y
       have i₂ := eq737229 (M.op y y)
       grind)
    | exact superpose eq737229 eq1004
    | exact resolve eq1004 eq737229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004 eq737229
  have eq741704 : ∀ X0 : G, (σ (M.op y y)) = (M.op (σ (M.op y y)) (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq17285 y x
       have i₂ := eq739118
       grind)
    | exact superpose eq739118 eq17285
    | exact resolve eq17285 eq739118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17285
  have eq741733 : ∀ X0 : G, (σ y) = (σ (M.op X0 X0)) ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq260628 y x
       have i₂ := eq739118
       grind)
    | exact superpose eq739118 eq260628
    | exact resolve eq260628 eq739118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260628
  have eq741837 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq741704 X0
       have i₂ := eq739118
       grind)
    | exact superpose eq739118 eq741704
    | exact resolve eq741704 eq739118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741704
  have eq931114 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ (σ (k y (τ X0))) = (M.op (σ y) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq741733 (τ X0)
       grind)
    | exact superpose eq741733 eq37
    | (have j1 := eq741733 (τ X0)
       grind)
    | exact resolve eq37 eq741733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq741733
  have eq931679 : ∀ X0 : G, (M.op (σ y) X0) = (σ (k y (τ X0))) ∨ (σ y) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq931114 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq931114
    | (have j0 := eq931114 X0
       grind)
    | exact resolve eq931114 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931114
  have eq931898 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ (σ y) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq931679 X0
       have i₂ := eq19 X0 y
       grind)
    | exact superpose eq19 eq931679
    | (have j0 := eq931679 X0
       grind)
    | exact resolve eq931679 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq931679
  have eq953024 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) ∨ (σ y) = (k (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq931898 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931898
  have eq957251 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq953024 (M.op X0 (σ y))
       have i₂ := eq741837 X0
       grind)
    | exact superpose eq741837 eq953024
    | (have j0 := eq953024 (M.op X0 (σ y))
       grind)
    | (have r₁ := eq953024 (M.op X0 (σ y))
       have r₂ := eq741837 X0
       grind)
    | exact resolve eq953024 eq741837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741837 eq953024
  have eq957328 : ∀ X0 : G, (σ y) = (k (σ y) (M.op X0 (σ y))) := by
    intro X0
    first
    | (have j0 := eq957251 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957251
  have eq957611 : ∀ X0 X1 : G, (τ (k X0 (σ y))) = (k (τ X0) (k y (τ (M.op X1 (σ y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq40 y (M.op X1 (σ y)) X0
       have i₂ := eq957328 X1
       grind)
    | exact superpose eq957328 eq40
    | exact resolve eq40 eq957328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq957808 : ∀ X0 X1 : G, (k (τ X0) y) = (k (τ X0) (k y (τ (M.op X1 (σ y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq957611 X0 X1
       have i₂ := eq27 X0 y
       grind)
    | exact superpose eq27 eq957611
    | exact resolve eq957611 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957611
  have eq984390 : ∀ X0 X1 : G, (σ (k (τ X0) y)) = (M.op (σ (τ X0)) (k (σ y) (M.op X1 (σ y)))) ∨ (σ (τ X0)) = (M.op (k (σ y) (M.op X1 (σ y))) (k (σ y) (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq85308 (τ X0) y (M.op X1 (σ y))
       have i₂ := eq957808 X0 X1
       grind)
    | exact superpose eq957808 eq85308
    | (have j0 := eq85308 (τ X0) y (M.op X1 (σ y))
       grind)
    | exact resolve eq85308 eq957808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85308 eq957808
  have eq984523 : ∀ X0 X1 : G, (σ (k (τ X0) y)) = (M.op (σ (τ X0)) (σ y)) ∨ (σ (τ X0)) = (M.op (k (σ y) (M.op X1 (σ y))) (k (σ y) (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq984390 X0 X1
       have i₂ := eq957328 X1
       grind)
    | exact superpose eq957328 eq984390
    | (have j0 := eq984390 X0 X1
       grind)
    | exact resolve eq984390 eq957328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984390
  have eq984818 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (σ (k (τ X0) y)) ∨ (σ (τ X0)) = (M.op (k (σ y) (M.op X1 (σ y))) (k (σ y) (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq984523 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq984523
    | (have j0 := eq984523 X0 X1
       grind)
    | exact resolve eq984523 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984523
  have eq985074 : ∀ X0 X1 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ (τ X0)) = (M.op (k (σ y) (M.op X1 (σ y))) (k (σ y) (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq984818 X0 X1
       have i₂ := eq18 X0 y
       grind)
    | exact superpose eq18 eq984818
    | (have j0 := eq984818 X0 X1
       grind)
    | exact resolve eq984818 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq984818
  have eq985146 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ y) (σ y)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq985074 X0 X0
       have i₂ := eq957328 X0
       grind)
    | exact superpose eq957328 eq985074
    | (have j0 := eq985074 X0 x
       grind)
    | exact resolve eq985074 eq957328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957328 eq985074
  have eq985188 : ∀ X0 : G, (σ (τ X0)) = (σ (k y y)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq985146 X0
       have i₂ := eq12937 y
       grind)
    | exact superpose eq12937 eq985146
    | (have j0 := eq985146 X0
       grind)
    | exact resolve eq985146 eq12937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985146
  have eq985208 : ∀ X0 : G, (σ (τ X0)) = (σ (M.op y y)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq985188 X0
       have i₂ := eq13070 y
       grind)
    | exact superpose eq13070 eq985188
    | (have j0 := eq985188 X0
       grind)
    | exact resolve eq985188 eq13070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985188
  have eq985222 : ∀ X0 : G, (σ (τ X0)) = (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq985208 X0
       have i₂ := eq739118
       grind)
    | exact superpose eq739118 eq985208
    | (have j0 := eq985208 X0
       grind)
    | exact resolve eq985208 eq739118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985208
  have eq985232 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = X0 := by
    intro X0
    first
    | (have i₁ := eq985222 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq985222
    | (have j0 := eq985222 X0
       grind)
    | exact resolve eq985222 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985222
  have eq988115 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op X0 (σ y))) ∨ (σ y) = X0 := by
    intro X0
    first
    | (have i₁ := eq27 X0 y
       have i₂ := eq985232 X0
       grind)
    | exact superpose eq985232 eq27
    | (have j1 := eq985232 X0
       grind)
    | exact resolve eq27 eq985232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq985232
  have eq989362 : (τ (σ y)) = (k (τ (σ x)) y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq988115 (σ x)
       have i₂ := eq555876
       grind)
    | exact superpose eq555876 eq988115
    | (have j0 := eq988115 (σ x)
       grind)
    | exact resolve eq988115 eq555876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555876 eq988115
  have eq990013 : (τ (σ y)) = (k (τ (σ x)) y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq989362
       have r₂ := eq566488
       grind)
    | exact resolve eq989362 eq566488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989362
  have eq990104 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq990013
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq990013
    | exact resolve eq990013 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990013
  have eq990152 : y = (k x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq990104
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq990104
    | exact resolve eq990104 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990104
  have eq990176 : (σ x) = (σ y) ∨ y = (k x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq990152
       have i₂ := eq739118
       grind)
    | exact superpose eq739118 eq990152
    | exact resolve eq990152 eq739118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990152
  have eq990194 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq990176
       have i₂ := eq739118
       grind)
    | exact superpose eq739118 eq990176
    | exact resolve eq990176 eq739118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990176
  have eq996106 : y ≠ y ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq721 x y
       have i₂ := eq990194
       grind)
    | exact superpose eq990194 eq721
    | (have j0 := eq721 x y
       grind)
    | (have r₁ := eq721 x y
       have r₂ := eq990194
       grind)
    | exact resolve eq721 eq990194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721 eq990194
  have eq996180 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq996106
  have eq996266 : x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq996180
       have i₂ := eq739118
       grind)
    | exact superpose eq739118 eq996180
    | exact resolve eq996180 eq739118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996180
  have eq996267 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq996266
  have eq996299 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq560585
       have i₂ := eq996267
       grind)
    | exact superpose eq996267 eq560585
    | exact resolve eq560585 eq996267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560585 eq996267
  have eq996407 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq996299
  have eq996425 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq996407
       have r₂ := eq566488
       grind)
    | exact resolve eq996407 eq566488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566488 eq996407
  have eq996433 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq996425
       have i₂ := eq739118
       grind)
    | exact superpose eq739118 eq996425
    | exact resolve eq996425 eq739118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996425
  have eq996439 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq996433
       have i₂ := eq739118
       grind)
    | exact superpose eq739118 eq996433
    | exact resolve eq996433 eq739118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739118 eq996433
  have eq996440 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq996439
  have eq999957 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq996440
       grind)
    | exact superpose eq996440 eq16
    | exact resolve eq16 eq996440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996440
  have eq1000187 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq999957
       have i₂ := eq12937 x
       grind)
    | exact superpose eq12937 eq999957
    | exact resolve eq999957 eq12937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999957
  have eq1000189 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1000187
       have i₂ := eq13070 x
       grind)
    | exact superpose eq13070 eq1000187
    | exact resolve eq1000187 eq13070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000187
  have eq1000190 : (σ x) = (σ y) := by grind
  clear eq1000189
  have eq1000195 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1000190
       grind)
    | exact superpose eq1000190 eq16
    | exact resolve eq16 eq1000190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1000241 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1000190
       grind)
    | exact superpose eq1000190 eq10
    | exact resolve eq10 eq1000190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000190
  have eq1000829 : x = y := by
    first
    | (have i₁ := eq1000241
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1000241
    | exact resolve eq1000241 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000241
  have eq1000836 : (σ (M.op x y)) ≠ (σ (k x x)) := by
    first
    | (have i₁ := eq1000195
       have i₂ := eq12937 x
       grind)
    | exact superpose eq12937 eq1000195
    | exact resolve eq1000195 eq12937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12937 eq1000195
  have eq1001013 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1000836
       have i₂ := eq13070 x
       grind)
    | exact superpose eq13070 eq1000836
    | exact resolve eq1000836 eq13070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13070 eq1000836
  have eq1001158 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1001013
       have i₂ := eq1000829
       grind)
    | exact superpose eq1000829 eq1001013
    | exact resolve eq1001013 eq1000829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000829 eq1001013
  have eq1001159 : False := by grind
  exact eq1001159

/-- `Equation4494`: `x ◇ (y ◇ y) = (z ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_x_x_pyx_Equation4494 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4494 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4494.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq134 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq51
    | (have j0 := eq51 (M.op x y)
       grind)
    | exact resolve eq51 eq20
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
  have eq176 : x ≠ (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : (σ x) = (k (σ x) (σ (M.op x x))) := by
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
  have eq179 : (σ y) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq37 (M.op y y)
       have i₂ := eq175 y
       grind)
    | exact superpose eq175 eq37
    | exact resolve eq37 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq182 : (σ y) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq179
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq179
    | exact resolve eq179 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq183 : (σ x) = (k (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq178
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq178
    | exact resolve eq178 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
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
  clear eq108
  have eq220 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq32 eq209
    | exact resolve eq209 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq338 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq35
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
  have eq553 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq399 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq175 (σ X0)
       grind)
    | exact superpose eq175 eq399
    | exact resolve eq399 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq582 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq553 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq553
    | exact resolve eq553 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq691 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X3 X1) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 x X1 X3
       have i₂ := eq16 x X1 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op (M.op (M.op X0 X1) X1) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1) x
       have i₂ := eq16 x X1 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq694 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X1)) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 (M.op x X1)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 : G, (M.op X0 (M.op y y)) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq16 X2 X1 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1) x
       have i₂ := eq16 (M.op x (M.op X1 X1)) X1 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op X1 X1)
       have i₂ := eq16 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X2 X1) ∨ (k X1 (M.op X2 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X1 (M.op X2 X1)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq28
    | (have j0 := eq28 X1 (M.op X2 X1)
       grind)
    | (have r₁ := eq28 (M.op X1 X1) (M.op (M.op X2 X1) X1)
       have r₂ := eq16 (M.op (M.op X2 X1) X1) X1 X2
       grind)
    | exact resolve eq28 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq705 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (M.op X1 y) y) := by
    intro X1
    first
    | (have i₁ := eq16 x y X1
       have i₂ := eq695 x
       grind)
    | exact superpose eq695 eq16
    | exact resolve eq16 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq711 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op y y) (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op y y) x
       have i₂ := eq695 (M.op x (M.op y y))
       grind)
    | exact superpose eq695 eq16
    | exact resolve eq16 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq712 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq711 X0
       have i₂ := eq695 (M.op y y)
       grind)
    | exact superpose eq695 eq711
    | exact resolve eq711 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq719 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op X1 (σ y)) (σ y)) := by
    intro X1
    first
    | exact superpose eq696 eq16
    | exact resolve eq16 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq725 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X0 (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) := by
    intro X0
    first
    | exact superpose eq696 eq16
    | exact resolve eq16 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq726 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq696 eq725
    | exact resolve eq725 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq759 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ y) (σ y)) X0) ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = X0 ∨ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq696 eq11
    | (have j0 := eq11 (M.op (σ y) (σ y)) X0
       grind)
    | exact resolve eq11 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq763 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq764 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq765 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op X1 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq766 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq175
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq175 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq768 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X0)) = (M.op (k X0 X1) X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq770 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (k (M.op X0 X0) X1) ∨ (M.op X1 (M.op X0 X0)) = X1 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq11 (M.op X0 X0) X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 (M.op X0 X0) X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq772 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) ∨ (M.op X0 (M.op (M.op x y) y)) = X0 ∨ (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq712 x
       have i₂ := eq11 (M.op sF0 y) x
       grind)
    | exact superpose eq11 eq712
    | (have j1 := eq11 (M.op (M.op x y) y) X0
       grind)
    | exact resolve eq712 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq783 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (k y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq695 X0
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq695
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq695 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq790 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X0 (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq696 X0
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq696
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq696 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq792 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq793 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq794 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq793 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793
  have eq796 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X0 (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq790 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq801 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (k y y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq783 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783
  have eq806 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq766 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq807 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op X1 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq765 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq821 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) ∨ (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have j0 := eq772 X0
       have j1 := eq28 (M.op (M.op x y) y) X0
       grind)
    | (have r₁ := eq772 x
       have r₂ := eq28 (M.op (M.op x y) y) x
       grind)
    | (have r₁ := eq772 (M.op (M.op x y) y)
       have r₂ := eq28 (M.op (M.op x y) y) (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq772 (M.op (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) X0)
       have r₂ := eq28 X0 (M.op (M.op (M.op x y) y) (M.op (M.op x y) y))
       grind)
    | exact resolve eq772 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq824 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = X0 ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ y) (σ y)) X0) ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq696 eq759
    | (have j0 := eq759 X0
       grind)
    | exact resolve eq759 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq825 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ y) (σ y)) X0) ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq824 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq836 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | (have j0 := eq821 X0
       have j1 := eq13 (M.op (M.op x y) y) X0
       grind)
    | (have r₁ := eq821 x
       have r₂ := eq13 (M.op (M.op x y) y) x
       grind)
    | (have r₁ := eq821 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op (M.op (M.op x y) y) (M.op (M.op x y) y))
       grind)
    | exact resolve eq821 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq841 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq794 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq794
    | (have j0 := eq794 (σ X0)
       grind)
    | exact resolve eq794 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq849 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) X0) ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = X0 ∨ (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq726 eq11
    | (have j0 := eq11 (M.op (M.op (σ x) (σ y)) (σ y)) X0
       grind)
    | exact resolve eq11 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq851 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ X0 ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq726 eq28
    | (have j0 := eq28 (M.op (M.op (σ x) (σ y)) (σ y)) X0
       grind)
    | (have r₁ := eq28 (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq726 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact resolve eq28 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq855 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) X0) ∨ (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq849 X0
       have j1 := eq851 X0
       grind)
    | (have r₁ := eq849 X0
       have r₂ := eq851 (k (M.op (M.op (σ x) (σ y)) (σ y)) X0)
       grind)
    | (have r₁ := eq849 X0
       have r₂ := eq851 X0
       grind)
    | (have r₁ := eq849 (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq851 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact resolve eq849 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849 eq851
  have eq859 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | (have j0 := eq855 X0
       have j1 := eq13 (M.op (M.op (σ x) (σ y)) (σ y)) X0
       grind)
    | (have r₁ := eq855 x
       have r₂ := eq13 (M.op (M.op (σ x) (σ y)) (σ y)) x
       grind)
    | (have r₁ := eq855 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y)))
       grind)
    | exact resolve eq855 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq864 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (k (σ (M.op (M.op x y) y)) X0) := by
    intro X0
    first
    | exact superpose eq836 eq39
    | exact resolve eq39 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq874 : ∀ X0 : G, (τ (M.op (M.op (σ x) (σ y)) (σ y))) = (k (τ (M.op (M.op (σ x) (σ y)) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq859 eq338
    | exact resolve eq338 eq859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq880 : (τ (M.op (M.op (σ x) (σ y)) (σ y))) = (k (τ (M.op (M.op (σ x) (σ y)) (σ y))) x) := by
    first
    | exact superpose eq859 eq142
    | exact resolve eq142 eq859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq859
  have eq917 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X1) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq691 X2 X1 (M.op x X1)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq691
    | exact resolve eq691 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq1007 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op X1 X1)
       have i₂ := eq697 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq175 (M.op X1 X1)
       have i₂ := eq697 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq697 eq175
    | exact resolve eq175 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq1322 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X2 (M.op X1 X1)) ∨ (k X1 (M.op X2 (M.op X1 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X1 (M.op X2 (M.op X1 X1))
       have i₂ := eq694 X2 X1 X0
       grind)
    | exact superpose eq694 eq28
    | (have j0 := eq28 X1 (M.op X2 (M.op X1 X1))
       grind)
    | (have r₁ := eq28 (M.op X1 X1) (M.op (M.op X0 (M.op X1 X1)) X1)
       have r₂ := eq694 X0 X1 (M.op (M.op X0 (M.op X1 X1)) X1)
       grind)
    | (have r₁ := eq28 X1 (M.op X2 (M.op X1 X1))
       have r₂ := eq694 X2 X1 X2
       grind)
    | exact resolve eq28 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1339 : ∀ X1 X2 : G, (k X1 (M.op X2 (M.op X1 X1))) = X1 := by
    intro X1 X2
    first
    | (have j0 := eq1322 x X1 X2
       grind)
    | (have r₁ := eq1322 x X1 X2
       have r₂ := eq697 x X1 X2
       grind)
    | (have r₁ := eq1322 X2 X1 x
       have r₂ := eq697 x X1 X2
       grind)
    | exact resolve eq1322 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322
  have eq1353 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq763
       grind)
    | exact superpose eq763 eq40
    | exact resolve eq40 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq1355 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1353
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1353
    | exact resolve eq1353 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1353
  have eq1357 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1355
    | exact resolve eq1355 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1355
  have eq2040 : ∀ X0 X1 X3 : G, (M.op X3 (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq698 (M.op x X1) X1 X3
       have i₂ := eq698 x X1 X0
       grind)
    | exact superpose eq698 eq698
    | exact resolve eq698 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2075 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X1) = (M.op X3 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq698 X2 X1 X3
       have i₂ := eq697 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq698 X2 X1 X3
       have i₂ := eq697 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq697 eq698
    | exact resolve eq698 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2603 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1357 eq764
    | exact resolve eq764 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2613 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq2603
       have r₂ := eq27
       grind)
    | exact resolve eq2603 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2603
  have eq2620 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2613 eq220
    | exact resolve eq220 eq2613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq2613
  have eq2657 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq2620
    | exact resolve eq2620 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2620
  have eq2663 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq2657
       have r₂ := eq176
       grind)
    | exact resolve eq2657 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq2657
  have eq2664 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq2663
       have r₂ := eq13 y x
       grind)
    | exact resolve eq2663 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2663
  have eq2668 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq2664
       grind)
    | exact superpose eq2664 eq40
    | exact resolve eq40 eq2664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq2664
  have eq2671 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2668
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2668
    | exact resolve eq2668 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2668
  have eq2674 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq2671
       have r₂ := eq177
       grind)
    | exact resolve eq2671 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq2671
  have eq2678 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2674 eq1357
    | exact resolve eq1357 eq2674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357
  have eq2679 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2674 eq764
    | exact resolve eq764 eq2674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764 eq2674
  have eq2699 : x = (k y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2678
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq2678
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq2678 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2701 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq695 X0
       have i₂ := eq2678
       grind)
    | exact superpose eq2678 eq695
    | exact resolve eq695 eq2678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2703 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq705 y
       have i₂ := eq2678
       grind)
    | exact superpose eq2678 eq705
    | exact resolve eq705 eq2678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq2707 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op X1 x) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq694 X0 y x
       have i₂ := eq2678
       grind)
    | exact superpose eq2678 eq694
    | exact resolve eq694 eq2678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq2715 : x = (k y y) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq2678
       grind)
    | exact superpose eq2678 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq2678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2716 : ∀ X0 : G, (M.op x y) = (M.op X0 x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq2678
       grind)
    | exact superpose eq2678 eq16
    | exact resolve eq16 eq2678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2721 : x = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq699 y y
       have i₂ := eq2678
       grind)
    | exact superpose eq2678 eq699
    | exact resolve eq699 eq2678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq2722 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq917 X0 y y
       have i₂ := eq2678
       grind)
    | exact superpose eq2678 eq917
    | exact resolve eq917 eq2678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2678
  have eq2724 : x = (k y y) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2715
  have eq2725 : x = (k y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq2699
  have eq2727 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq2722 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2722
    | (have j0 := eq2722 X0
       grind)
    | exact resolve eq2722 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2722
  have eq2728 : x = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2721
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2721
    | exact resolve eq2721 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2721
  have eq2732 : ∀ X0 : G, (M.op x y) = (M.op X0 x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq2716 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2716
    | (have j0 := eq2716 X0
       grind)
    | exact resolve eq2716 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2716
  have eq2737 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2703
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2703
    | exact resolve eq2703 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2703
  have eq2739 : x = (k y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2724 eq2725
    | exact resolve eq2725 eq2724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2724 eq2725
  have eq2745 : x = (k y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2732 eq2739
    | exact resolve eq2739 eq2732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2739
  have eq2746 : x = (k y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2745
  have eq2748 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq2679
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq2679
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq2679 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2752 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2679 eq719
    | exact resolve eq719 eq2679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2761 : ∀ X0 : G, (σ x) = (k (σ x) (M.op X0 (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2679 eq1007
    | exact resolve eq1007 eq2679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq2762 : ∀ X0 : G, (σ y) = (k (σ y) (M.op X0 (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2679 eq1339
    | exact resolve eq1339 eq2679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339
  have eq2764 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2679 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq2679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2765 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2679 eq16
    | exact resolve eq16 eq2679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2771 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2679 eq917
    | exact resolve eq917 eq2679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq2773 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2764
  have eq2774 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq2748
  have eq2776 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq2771
    | (have j0 := eq2771 X0
       grind)
    | exact resolve eq2771 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2771
  have eq2781 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq2765
    | (have j0 := eq2765 X0
       grind)
    | exact resolve eq2765 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2765
  have eq2786 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq2752
    | exact resolve eq2752 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2752
  have eq2788 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2773 eq2774
    | exact resolve eq2774 eq2773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2773 eq2774
  have eq2849 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2728 eq42
    | exact resolve eq42 eq2728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2728
  have eq2851 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2849
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2849
    | exact resolve eq2849 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2849
  have eq2965 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq2746
       grind)
    | exact superpose eq2746 eq41
    | exact resolve eq41 eq2746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2746
  have eq2973 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2965
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2965
    | exact resolve eq2965 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2965
  have eq2975 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2973
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2973
    | exact resolve eq2973 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2973
  have eq5514 : ∀ X0 : G, (σ x) = (k (σ x) (k (σ x) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ x)) = X0 ∨ (M.op (σ x) (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2761 x
       have i₂ := eq11 sF2 x
       grind)
    | exact superpose eq11 eq2761
    | (have j1 := eq11 (σ x) X0
       grind)
    | exact resolve eq2761 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2761
  have eq5530 : ∀ X0 : G, (σ x) = (k (σ x) (k (σ x) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = X0 ∨ (M.op (σ x) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq2781 eq5514
    | (have j0 := eq5514 X0
       grind)
    | exact resolve eq5514 eq2781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5514
  have eq5532 : ∀ X0 : G, (σ x) = (k (σ x) (k (σ x) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = X0 ∨ (M.op (σ x) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq2781 eq5530
    | (have j0 := eq5530 X0
       grind)
    | exact resolve eq5530 eq2781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5530
  have eq5533 : ∀ X0 : G, (σ x) = (k (σ x) (k (σ x) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq5532 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5532
  have eq5538 : ∀ X0 : G, (σ y) = (k (σ y) (k (σ x) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ x)) = X0 ∨ (M.op (σ x) (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2762 x
       have i₂ := eq11 sF2 x
       grind)
    | exact superpose eq11 eq2762
    | (have j1 := eq11 (σ x) X0
       grind)
    | exact resolve eq2762 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2762
  have eq5559 : ∀ X0 : G, (σ y) = (k (σ y) (k (σ x) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = X0 ∨ (M.op (σ x) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq2781 eq5538
    | (have j0 := eq5538 X0
       grind)
    | exact resolve eq5538 eq2781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5538
  have eq5563 : ∀ X0 : G, (σ y) = (k (σ y) (k (σ x) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = X0 ∨ (M.op (σ x) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq2781 eq5559
    | (have j0 := eq5559 X0
       grind)
    | exact resolve eq5559 eq2781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5559
  have eq5564 : ∀ X0 : G, (σ y) = (k (σ y) (k (σ x) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq5563 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5563
  have eq5569 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (k (σ x) X0) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ x)) = X0 ∨ (M.op (σ x) (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2776 x
       have i₂ := eq11 sF2 x
       grind)
    | exact superpose eq11 eq2776
    | (have j1 := eq11 (σ x) X0
       grind)
    | exact resolve eq2776 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2776
  have eq5605 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (k (σ x) X0) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = X0 ∨ (M.op (σ x) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq2781 eq5569
    | (have j0 := eq5569 X0
       grind)
    | exact resolve eq5569 eq2781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5569
  have eq5609 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (k (σ x) X0) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = X0 ∨ (M.op (σ x) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq2781 eq5605
    | (have j0 := eq5605 X0
       grind)
    | exact resolve eq5605 eq2781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5605
  have eq5610 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (k (σ x) X0) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq5609 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5609
  have eq6637 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X1 X1))) = (M.op (M.op (M.op X3 X1) X1) (M.op X1 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq693 X3 X1 X2
       have i₂ := eq697 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq693 X3 X1 X2
       have i₂ := eq697 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq697 eq693
    | exact resolve eq693 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693 eq697
  have eq7161 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq2975 eq768
    | (have j0 := eq768 (σ y) (σ y) x
       grind)
    | exact resolve eq768 eq2975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7356 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq7161 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7161
  have eq7425 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq696 eq7356
    | exact resolve eq7356 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7356
  have eq7514 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq7425
    | exact resolve eq7425 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7425
  have eq12868 : ∀ X0 X1 : G, (k x X1) = (M.op (M.op X0 x) y) ∨ (M.op (M.op X0 x) y) = X1 ∨ (M.op x x) = X1 ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq11 x X0
       have i₂ := eq2707 X0 X1
       grind)
    | exact superpose eq2707 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq2707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2707
  have eq13000 : ∀ X0 X1 : G, (k x X1) = (M.op (M.op X0 x) y) ∨ (M.op (M.op X0 x) y) = X1 ∨ (M.op (M.op x y) y) = X1 ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq2701 eq12868
    | (have j0 := eq12868 X0 X1
       grind)
    | exact resolve eq12868 eq2701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2701 eq12868
  have eq13061 : ∀ X0 X1 : G, (M.op x y) = (k x X1) ∨ (M.op (M.op X0 x) y) = X1 ∨ (M.op (M.op x y) y) = X1 ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq2727 eq13000
    | (have j0 := eq13000 X0 X1
       grind)
    | exact resolve eq13000 eq2727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2727 eq13000
  have eq13095 : ∀ X1 : G, (M.op x y) = (k x X1) ∨ (M.op (M.op x y) y) = X1 ∨ (M.op (M.op x y) y) = X1 ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X1
    first
    | exact superpose eq2732 eq13061
    | (have j0 := eq13061 x X1
       grind)
    | exact resolve eq13061 eq2732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13061
  have eq13096 : ∀ X1 : G, (M.op x y) = (k x X1) ∨ (M.op (M.op x y) y) = X1 ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X1
    first
    | (have j0 := eq13095 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13095
  have eq19573 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2788 eq116
    | exact resolve eq116 eq2788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2788
  have eq19591 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq30 eq19573
    | exact resolve eq19573 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19573
  have eq19917 : ∀ X0 : G, (σ x) ≠ (k (σ x) X0) ∨ (k (σ x) X0) = (M.op (k (σ x) X0) (σ x)) ∨ (k (σ x) X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq5533 eq792
    | (have j0 := eq792 (k (σ x) X0) (σ x)
       have j1 := eq5533 (σ x)
       grind)
    | (have r₁ := eq792 (M.op (σ x) (σ y)) x
       have r₂ := eq5533 (k x (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq792 eq5533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792 eq5533
  have eq19922 : ∀ X0 : G, (σ x) ≠ (k (σ x) X0) ∨ (M.op (σ x) (σ y)) = (k (σ x) X0) ∨ (k (σ x) X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq2781 eq19917
    | (have j0 := eq19917 X0
       grind)
    | exact resolve eq19917 eq2781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19917
  have eq19934 : ∀ X0 : G, (σ x) ≠ (k (σ x) X0) ∨ (M.op (σ x) (σ y)) = (k (σ x) X0) ∨ (M.op (σ x) (σ y)) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq2781 eq19922
    | (have j0 := eq19922 X0
       grind)
    | exact resolve eq19922 eq2781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19922
  have eq19935 : ∀ X0 : G, (σ x) ≠ (k (σ x) X0) ∨ (M.op (σ x) (σ y)) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq19934 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19934
  have eq20009 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ y) (k (σ x) X0)) ∨ (M.op (σ x) (σ y)) = (k (σ x) X0) ∨ (k (σ x) X0) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq5610 eq11
    | (have j0 := eq11 (σ y) (σ x)
       have j1 := eq5610 (k (σ y) (k (σ x) X0))
       grind)
    | exact resolve eq11 eq5610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5610
  have eq20044 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ y) (k (σ x) X0)) ∨ (M.op (σ x) (σ y)) = (k (σ x) X0) ∨ (σ x) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq2679 eq20009
    | (have j0 := eq20009 X0
       grind)
    | exact resolve eq20009 eq2679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20009
  have eq20047 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ y) (k (σ x) X0)) ∨ (M.op (σ x) (σ y)) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq20044 X0
       have j1 := eq19935 X0
       grind)
    | (have r₁ := eq20044 X0
       have r₂ := eq19935 X0
       grind)
    | exact resolve eq20044 eq19935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19935 eq20044
  have eq20048 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq5564 eq20047
    | (have j0 := eq20047 X0
       have j1 := eq5564 (σ y)
       grind)
    | exact resolve eq20047 eq5564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5564 eq20047
  have eq20049 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq20048 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20048
  have eq20096 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20049 eq2851
    | (have j1 := eq20049 (σ x)
       grind)
    | exact resolve eq2851 eq20049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2851
  have eq20104 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20049 eq99
    | (have j1 := eq20049 (σ y)
       grind)
    | exact resolve eq99 eq20049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq20049
  have eq20151 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20104
  have eq20158 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq20096
  have eq20210 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq20158
       have r₂ := eq27
       grind)
    | exact resolve eq20158 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20158
  have eq20227 : (k (σ x) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq20151
       grind)
    | exact superpose eq20151 eq41
    | exact resolve eq41 eq20151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20151
  have eq20231 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20227
       have i₂ := eq14 sF4
       grind)
    | exact superpose eq14 eq20227
    | exact resolve eq20227 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20227
  have eq20233 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20231
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20231
    | exact resolve eq20231 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20231
  have eq20432 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq22067 : x = (M.op x y) ∨ x = (M.op x x) ∨ (k x x) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq806 x
       have i₂ := eq13096 (k x x)
       grind)
    | exact superpose eq13096 eq806
    | (have j0 := eq806 x
       have j1 := eq13096 (k x x)
       grind)
    | exact resolve eq806 eq13096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806 eq13096
  have eq22074 : x = (M.op x y) ∨ x = (M.op x x) ∨ (k x x) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq22067
  have eq22141 : x = (M.op x y) ∨ x = (M.op x y) ∨ (k x x) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2732 eq22074
    | exact resolve eq22074 eq2732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2732 eq22074
  have eq22142 : x = (M.op x y) ∨ (k x x) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq22141
  have eq22185 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2737 eq22142
    | exact resolve eq22142 eq2737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2737 eq22142
  have eq24546 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq19591 eq2781
    | exact resolve eq2781 eq19591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2781 eq19591
  have eq24592 : x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24546
  have eq24623 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq24592
       grind)
    | exact superpose eq24592 eq41
    | exact resolve eq41 eq24592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24628 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq768 y y X0
       have i₂ := eq24592
       grind)
    | exact superpose eq24592 eq768
    | (have j0 := eq768 y y x
       grind)
    | exact resolve eq768 eq24592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24632 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op y y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq24628 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24628
  have eq24633 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24632 x
       have i₂ := eq695 x
       grind)
    | exact superpose eq695 eq24632
    | exact resolve eq24632 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24632
  have eq24635 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24623
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24623
    | exact resolve eq24623 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24623
  have eq24637 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24633
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24633
    | exact resolve eq24633 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24633
  have eq24638 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24635
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24635
    | exact resolve eq24635 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24635
  have eq24970 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20210 eq7514
    | exact resolve eq7514 eq20210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7514 eq20210
  have eq25007 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24970
  have eq25044 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25007 eq28
    | (have j0 := eq28 (σ y) (σ y)
       grind)
    | (have r₁ := eq28 (σ y) (σ y)
       have r₂ := eq25007
       grind)
    | (have r₁ := eq28 y x
       have r₂ := eq25007
       grind)
    | (have r₁ := eq28 (σ y) (σ x)
       have r₂ := eq25007
       grind)
    | exact resolve eq28 eq25007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25007
  have eq25061 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq25044
  have eq25076 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2975 eq25061
    | exact resolve eq25061 eq2975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2975 eq25061
  have eq25093 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq25076
       have r₂ := eq20432
       grind)
    | exact resolve eq25076 eq20432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20432 eq25076
  have eq25117 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25093 eq880
    | exact resolve eq880 eq25093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq25130 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq25117
    | exact resolve eq25117 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25117
  have eq25144 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25093 eq25130
    | exact resolve eq25130 eq25093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25093 eq25130
  have eq25157 : x = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq25144
    | exact resolve eq25144 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25144
  have eq25160 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22185 eq25157
    | exact resolve eq25157 eq22185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22185 eq25157
  have eq25161 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq25160
  have eq25409 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25161 eq29
    | exact resolve eq29 eq25161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq25419 : (k (M.op x y) (M.op x y)) = (τ (k (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25161 eq134
    | exact resolve eq134 eq25161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq25490 : (k y y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq116 eq25419
    | exact resolve eq25419 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25419
  have eq25500 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq25409
    | exact resolve eq25409 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25409
  have eq25506 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq25500
       grind)
    | exact superpose eq25500 eq18
    | exact resolve eq18 eq25500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25517 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq712 X0
       have i₂ := eq25500
       grind)
    | exact superpose eq25500 eq712
    | exact resolve eq712 eq25500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25523 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op x y))) = (k (σ (M.op (M.op x y) (M.op x y))) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq864 X0
       have i₂ := eq25500
       grind)
    | exact superpose eq25500 eq864
    | exact resolve eq864 eq25500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25558 : x = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24592
       have i₂ := eq25500
       grind)
    | exact superpose eq25500 eq24592
    | exact resolve eq24592 eq25500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24592
  have eq25619 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq25506 eq807
    | (have j0 := eq807 (M.op x y) x x
       grind)
    | exact resolve eq807 eq25506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27193 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op X0 (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq25517 X0
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq25517
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq25517 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27306 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op X0 (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq27193 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27193
  have eq28410 : (σ (M.op (M.op x y) (M.op x y))) ≠ (σ (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25523 eq794
    | (have j0 := eq794 (σ (M.op (M.op x y) (M.op x y)))
       grind)
    | (have r₁ := eq794 (σ (M.op (M.op x y) (M.op x y)))
       have r₂ := eq25523 (σ (M.op (M.op x y) (M.op x y)))
       grind)
    | exact resolve eq794 eq25523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25523
  have eq28425 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by grind
  clear eq28410
  have eq31300 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24637
       have i₂ := eq25500
       grind)
    | exact superpose eq25500 eq24637
    | exact resolve eq24637 eq25500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25500
  have eq31305 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24637 eq712
    | exact resolve eq712 eq24637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24637
  have eq31341 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq31300
  have eq31363 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq31341 eq25517
    | exact resolve eq25517 eq31341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25517
  have eq31414 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq31341 eq702
    | exact resolve eq702 eq31341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq31341
  have eq31443 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq31363 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31363
  have eq31456 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq25558 eq31414
    | (have j0 := eq31414 X0
       grind)
    | exact resolve eq31414 eq25558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25558 eq31414
  have eq31457 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq31456 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31456
  have eq31473 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq31457 x
       have r₂ := eq31443 x
       grind)
    | exact resolve eq31457 eq31443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31443 eq31457
  have eq31485 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31473 eq27
    | exact resolve eq27 eq31473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31473
  have eq31533 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq31485
       have r₂ := eq25161
       grind)
    | exact resolve eq31485 eq25161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31485
  have eq31717 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31533 eq27
    | exact resolve eq27 eq31533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31782 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25161 eq31717
    | exact resolve eq31717 eq25161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31717
  have eq31783 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq31782
  have eq38547 : ∀ X0 : G, (k (σ x) X0) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2679 eq825
    | (have j0 := eq825 (k (σ x) X0)
       grind)
    | exact resolve eq825 eq2679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825 eq2679
  have eq38616 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) X0) ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2786 eq38547
    | (have j0 := eq38547 X0
       grind)
    | exact resolve eq38547 eq2786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38547
  have eq38965 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x x)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38616 eq183
    | (have j1 := eq38616 (σ (M.op x x))
       grind)
    | exact resolve eq183 eq38616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq38616
  have eq39037 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x x)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq38965
  have eq39104 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31533 eq39037
    | exact resolve eq39037 eq31533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39037
  have eq39139 : (M.op (σ x) (σ y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2786 eq39104
    | exact resolve eq39104 eq2786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2786 eq39104
  have eq43868 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31305 eq39139
    | exact resolve eq39139 eq31305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31305 eq39139
  have eq43875 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq43868
  have eq43893 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq43875
    | exact resolve eq43875 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43875
  have eq43940 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq43893
       have r₂ := eq27
       grind)
    | exact resolve eq43893 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43893
  have eq43964 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq182
       have i₂ := eq43940
       grind)
    | exact superpose eq43940 eq182
    | exact resolve eq182 eq43940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq43993 : ∀ X0 : G, (M.op y y) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq43940
       grind)
    | exact superpose eq43940 eq16
    | exact resolve eq16 eq43940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44025 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq43940 eq43993
    | exact resolve eq43993 eq43940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43940 eq43993
  have eq44033 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43964
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq43964
    | exact resolve eq43964 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43964
  have eq44044 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24638 eq44033
    | exact resolve eq44033 eq24638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24638 eq44033
  have eq44953 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq864 X0
       have i₂ := eq44025 sF0
       grind)
    | exact superpose eq44025 eq864
    | exact resolve eq864 eq44025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864 eq44025
  have eq44989 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq44953 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq44953
    | (have j0 := eq44953 X0
       grind)
    | exact resolve eq44953 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44953
  have eq45023 : ∀ X0 : G, (σ x) = (k (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq44044 eq44989
    | exact resolve eq44989 eq44044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44044 eq44989
  have eq45168 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45023 eq20233
    | exact resolve eq20233 eq45023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20233 eq45023
  have eq45190 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq45168
  have eq45226 : ∀ X0 : G, (τ (M.op (σ y) (σ y))) = (k (τ (M.op (σ y) (σ y))) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq45190 eq874
    | exact resolve eq874 eq45190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq45251 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq46060 : (τ (M.op (σ y) (σ y))) ≠ (τ (M.op (σ y) (σ y))) ∨ (τ (M.op (σ y) (σ y))) = (M.op (τ (M.op (σ y) (σ y))) (τ (M.op (σ y) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45226 eq794
    | (have j0 := eq794 (τ (M.op (σ y) (σ y)))
       grind)
    | (have r₁ := eq794 (τ (M.op (σ y) (σ y)))
       have r₂ := eq45226 (τ (M.op (σ y) (σ y)))
       grind)
    | exact resolve eq794 eq45226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794 eq45226
  have eq46076 : (τ (M.op (σ y) (σ y))) = (M.op (τ (M.op (σ y) (σ y))) (τ (M.op (σ y) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq46060
  have eq64573 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq27306 eq25619
    | exact resolve eq25619 eq27306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25619
  have eq64574 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq27306 eq807
    | (have j0 := eq807 (M.op x y) x x
       grind)
    | exact resolve eq807 eq27306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807 eq27306
  have eq64665 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq64574 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64574
  have eq64666 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq64573
  have eq66142 : ∀ X0 : G, (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op X0 (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28425 eq698
    | exact resolve eq698 eq28425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66183 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op x y))) = (M.op X0 (σ (M.op (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28425 eq66142
    | exact resolve eq66142 eq28425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28425 eq66142
  have eq66213 : ∀ X0 : G, (σ (k (M.op x y) (M.op x y))) = (M.op X0 (σ (k (M.op x y) (M.op x y)))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq66183 X0
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq66183
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq66183 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66328 : ∀ X0 : G, (σ (k (M.op x y) (M.op x y))) = (M.op X0 (σ (k (M.op x y) (M.op x y)))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq66213 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66213
  have eq66364 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq42 eq66328
    | exact resolve eq66328 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq66328
  have eq66369 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq66364
    | (have j0 := eq66364 X0
       grind)
    | exact resolve eq66364 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66364
  have eq66372 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op X0 (k (σ y) (σ y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq25161 eq66369
    | exact resolve eq66369 eq25161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66369
  have eq67572 : ∀ X0 : G, (M.op (τ (M.op (σ y) (σ y))) (τ (M.op (σ y) (σ y)))) = (M.op X0 (M.op (τ (M.op (σ y) (σ y))) (τ (M.op (σ y) (σ y))))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq46076 eq698
    | exact resolve eq698 eq46076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq67608 : ∀ X0 : G, (τ (M.op (σ y) (σ y))) = (M.op X0 (τ (M.op (σ y) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq46076 eq67572
    | exact resolve eq67572 eq46076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67572
  have eq67627 : ∀ X0 : G, (τ (k (σ y) (σ y))) = (M.op X0 (τ (k (σ y) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq67608 X0
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq67608
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq67608 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67608
  have eq67741 : ∀ X0 : G, (τ (k (σ y) (σ y))) = (M.op X0 (τ (k (σ y) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq67627 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67627
  have eq67772 : ∀ X0 : G, (k y y) = (M.op X0 (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq116 eq67741
    | exact resolve eq67741 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67741
  have eq70709 : (k (M.op x y) (M.op x y)) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq64666 eq64665
    | exact resolve eq64665 eq64666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64665 eq64666
  have eq70852 : (k (M.op x y) (M.op x y)) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq70709
  have eq70911 : (k (M.op x y) (M.op x y)) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq28 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq70852
       have r₂ := eq28 (M.op x y) (k (M.op x y) (M.op x y))
       grind)
    | (have r₁ := eq70852
       have r₂ := eq28 y x
       grind)
    | (have r₁ := eq70852
       have r₂ := eq28 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq70852 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq70852
  have eq71158 : (k (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq66372 eq796
    | exact resolve eq796 eq66372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796 eq66372
  have eq71304 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq31533 eq71158
    | exact resolve eq71158 eq31533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71158
  have eq71339 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26 eq71304
    | exact resolve eq71304 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71304
  have eq71347 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq31533 eq71339
    | exact resolve eq71339 eq31533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71339
  have eq94755 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X1 (σ y))) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq71347 eq2075
    | exact resolve eq2075 eq71347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94764 : ∀ X0 X1 : G, (M.op (M.op (σ y) (σ y)) (σ y)) = (M.op X0 (M.op X1 (σ y))) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq71347 eq6637
    | exact resolve eq6637 eq71347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6637
  have eq94789 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X0 (M.op X1 (σ y))) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq719 eq94764
    | exact resolve eq94764 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719 eq94764
  have eq94793 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op X1 (σ y))) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq71347 eq94755
    | exact resolve eq94755 eq71347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71347 eq94755
  have eq94818 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X1 (σ y))) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq31533 eq94789
    | exact resolve eq94789 eq31533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94789
  have eq94831 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X1 (σ y))) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq94818
    | (have j0 := eq94818 X0 X1
       grind)
    | exact resolve eq94818 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94818
  have eq94838 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq94793 eq94831
    | exact resolve eq94831 eq94793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94793 eq94831
  have eq94842 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq31533 eq94838
    | exact resolve eq94838 eq31533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94838
  have eq94845 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq94842
       have r₂ := eq31783
       grind)
    | exact resolve eq94842 eq31783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94842
  have eq94929 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq94845 eq116
    | exact resolve eq116 eq94845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq94845
  have eq94990 : x = (k y y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq30 eq94929
    | exact resolve eq94929 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq94929
  have eq94997 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq25490 eq94990
    | exact resolve eq94990 eq25490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25490 eq94990
  have eq95114 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq94997 eq66183
    | exact resolve eq66183 eq94997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66183 eq94997
  have eq95219 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq95114 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95114
  have eq95279 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq95219
    | (have j0 := eq95219 X0
       grind)
    | exact resolve eq95219 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95219
  have eq95306 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq25161 eq95279
    | exact resolve eq95279 eq25161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25161 eq95279
  have eq96380 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq95306 eq26
    | (have j1 := eq95306 (σ x)
       grind)
    | exact resolve eq26 eq95306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95306
  have eq96536 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq31533 eq96380
    | exact resolve eq96380 eq31533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31533 eq96380
  have eq96611 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq96536
       have r₂ := eq31783
       grind)
    | exact resolve eq96536 eq31783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31783 eq96536
  have eq96693 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq96611 eq70911
    | exact resolve eq70911 eq96611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70911 eq96611
  have eq96736 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq96693
  have eq96762 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25506 eq96736
    | exact resolve eq96736 eq25506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25506 eq96736
  have eq96763 : x = (M.op x y) := by grind
  clear eq96762
  have eq96776 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq96763
       grind)
    | exact superpose eq96763 eq18
    | exact resolve eq18 eq96763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq96777 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq96763
       grind)
    | exact superpose eq96763 eq22
    | exact resolve eq22 eq96763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq96763
  have eq98435 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq96777 eq20
    | exact resolve eq20 eq96777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98712 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq96776 eq712
    | exact resolve eq712 eq96776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98714 : ∀ X0 : G, (M.op x y) = (k (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq96776 eq836
    | exact resolve eq836 eq96776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq98750 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op y y) X0) ∨ (M.op X0 (M.op y y)) = X0 ∨ (M.op (M.op y y) (M.op y y)) = X0 := by
    intro X0
    first
    | exact superpose eq96776 eq770
    | (have j0 := eq770 y X0 x
       grind)
    | exact resolve eq770 eq96776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq98774 : ∀ X0 : G, (M.op x y) = (k (M.op y y) X0) ∨ (M.op X0 (M.op y y)) = X0 ∨ (M.op (M.op y y) (M.op y y)) = X0 := by
    intro X0
    first
    | exact superpose eq96776 eq98750
    | (have j0 := eq98750 X0
       grind)
    | exact resolve eq98750 eq96776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98750
  have eq98786 : ∀ X0 : G, (M.op (M.op x y) y) = X0 ∨ (M.op x y) = (k (M.op y y) X0) ∨ (M.op (M.op y y) (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq98774 X0
       have i₂ := eq695 X0
       grind)
    | exact superpose eq695 eq98774
    | (have j0 := eq98774 X0
       grind)
    | exact resolve eq98774 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98774
  have eq98792 : ∀ X0 : G, (M.op x y) = X0 ∨ (M.op x y) = (k (M.op y y) X0) ∨ (M.op (M.op y y) (M.op y y)) = X0 := by
    intro X0
    first
    | exact superpose eq96776 eq98786
    | (have j0 := eq98786 X0
       grind)
    | exact resolve eq98786 eq96776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98786
  have eq98794 : ∀ X0 : G, (M.op (M.op x y) y) = X0 ∨ (M.op x y) = X0 ∨ (M.op x y) = (k (M.op y y) X0) := by
    intro X0
    first
    | (have i₁ := eq98792 X0
       have i₂ := eq695 (M.op y y)
       grind)
    | exact superpose eq695 eq98792
    | (have j0 := eq98792 X0
       grind)
    | exact resolve eq98792 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695 eq98792
  have eq98795 : ∀ X0 : G, (M.op x y) = X0 ∨ (M.op x y) = X0 ∨ (M.op x y) = (k (M.op y y) X0) := by
    intro X0
    first
    | exact superpose eq96776 eq98794
    | (have j0 := eq98794 X0
       grind)
    | exact resolve eq98794 eq96776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98794
  have eq98796 : ∀ X0 : G, (M.op x y) = (k (M.op y y) X0) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have j0 := eq98795 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98795
  have eq99196 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq98714 eq841
    | (have j0 := eq841 (M.op x y)
       grind)
    | exact resolve eq841 eq98714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841 eq98714
  have eq99222 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq99196
  have eq99243 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq99222
    | exact resolve eq99222 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99222
  have eq99255 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq98435 eq99243
    | exact resolve eq99243 eq98435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99243
  have eq99598 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op X1 (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq99255 eq2075
    | exact resolve eq2075 eq99255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99619 : ∀ X0 X1 : G, (σ x) = (M.op X0 (M.op X1 (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq99255 eq99598
    | exact resolve eq99598 eq99255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99255 eq99598
  have eq108607 : (M.op x y) = (τ (M.op (σ (M.op y y)) (σ (M.op y y)))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq582 (M.op y y)
       have i₂ := eq98796 (τ (M.op (σ (M.op y y)) (σ (M.op y y))))
       grind)
    | exact superpose eq98796 eq582
    | (have j1 := eq98796 (τ (M.op (σ (M.op y y)) (σ (M.op y y))))
       grind)
    | exact resolve eq582 eq98796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582 eq98796
  have eq152606 : (σ (M.op x y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq14 (M.op (σ (M.op y y)) (σ (M.op y y)))
       have i₂ := eq108607
       grind)
    | exact superpose eq108607 eq14
    | exact resolve eq14 eq108607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108607
  have eq152648 : (σ (M.op x y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq152606
    | exact resolve eq152606 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152606
  have eq152659 : (σ x) = (M.op (σ (M.op y y)) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq98435 eq152648
    | exact resolve eq152648 eq98435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152648
  have eq152765 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op (σ x) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq2075 X0 (σ (M.op y y)) (σ (M.op y y)) x
       have i₂ := eq152659
       grind)
    | exact superpose eq152659 eq2075
    | exact resolve eq2075 eq152659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2075 eq152659
  have eq152793 : (σ x) = (M.op (σ x) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq99619 eq152765
    | exact resolve eq152765 eq99619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99619 eq152765
  have eq159195 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (M.op x y) y) (M.op (M.op x y) y))) = (M.op (M.op X1 (M.op (M.op (M.op x y) y) (M.op (M.op x y) y))) (k y y)) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq2040 X0 (k y y) x
       have i₂ := eq801 (k y y)
       grind)
    | exact superpose eq801 eq2040
    | exact resolve eq2040 eq801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801 eq2040
  have eq160625 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) y)) = (M.op (M.op X1 (M.op (M.op x y) y)) (k y y)) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq712 eq159195
    | exact resolve eq159195 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159195
  have eq160736 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) y)) = (M.op (M.op (M.op x y) y) (k y y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq712 eq160625
    | exact resolve eq160625 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712 eq160625
  have eq160777 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op x y) (k y y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq96776 eq160736
    | exact resolve eq160736 eq96776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96776 eq160736
  have eq160781 : (M.op x y) = (M.op (M.op x y) (k y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq98712 eq160777
    | exact resolve eq160777 eq98712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98712 eq160777
  have eq160799 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq160781 eq67772
    | exact resolve eq67772 eq160781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67772 eq160781
  have eq176736 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq160799 eq46076
    | exact resolve eq46076 eq160799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160799
  have eq176867 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ y = (M.op y y) := by grind
  clear eq176736
  have eq176959 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq32 eq176867
    | exact resolve eq176867 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176867
  have eq176960 : (M.op x y) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq176959
  have eq177030 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq176960
       grind)
    | exact superpose eq176960 eq41
    | exact resolve eq41 eq176960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq176960
  have eq177095 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq177030
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq177030
    | exact resolve eq177030 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177030
  have eq177105 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq177095
    | exact resolve eq177095 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq177095
  have eq177111 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq98435 eq177105
    | exact resolve eq177105 eq98435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177105
  have eq178701 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq177111 eq768
    | (have j0 := eq768 (σ y) (σ y) x
       grind)
    | exact resolve eq768 eq177111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768 eq177111
  have eq178705 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq178701 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178701
  have eq178718 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq696 eq178705
    | exact resolve eq178705 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696 eq178705
  have eq178739 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq178718
    | exact resolve eq178718 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178718
  have eq178754 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq45190 eq178739
    | exact resolve eq178739 eq45190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45190 eq178739
  have eq178755 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq178754
  have eq178954 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq178755 eq46076
    | exact resolve eq46076 eq178755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46076 eq178755
  have eq179085 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq178954
  have eq179180 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq32 eq179085
    | exact resolve eq179085 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq179085
  have eq179181 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq179180
  have eq179255 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq152793
       have i₂ := eq179181
       grind)
    | exact superpose eq179181 eq152793
    | exact resolve eq152793 eq179181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152793 eq179181
  have eq179387 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq179255
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq179255
    | exact resolve eq179255 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179255
  have eq179415 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq179387
    | exact resolve eq179387 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq179387
  have eq179416 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq179415
  have eq179439 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq179416 eq27
    | exact resolve eq27 eq179416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179416
  have eq179496 : y = (M.op x y) := by
    first
    | (have r₁ := eq179439
       have r₂ := eq98435
       grind)
    | exact resolve eq179439 eq98435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179439
  have eq179514 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq179496
       grind)
    | exact superpose eq179496 eq24
    | exact resolve eq24 eq179496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq179496
  have eq179707 : (σ x) = (σ y) := by
    first
    | exact superpose eq96777 eq179514
    | exact resolve eq179514 eq96777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96777 eq179514
  have eq179941 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq179707 eq45251
    | (have r₁ := eq45251
       have r₂ := eq179707
       grind)
    | exact resolve eq45251 eq179707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45251 eq179707
  have eq180035 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq179941
  have eq180211 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq180035 eq27
    | exact resolve eq27 eq180035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq180035
  have eq180264 : False := by grind
  exact eq180264
