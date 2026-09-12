import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_pxy_y_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = b :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
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
  have eq71 : y ≠ (M.op x y) ∨ y = (M.op x x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq108
    | exact resolve eq108 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq110
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq110
    | exact resolve eq110 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq626 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq89 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq9864 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq111 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9865 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq9864
    | exact resolve eq9864 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9864
  have eq9876 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq9865
       have r₂ := eq28
       grind)
    | exact resolve eq9865 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9865
  have eq9878 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq9876
    | exact resolve eq9876 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9876
  have eq9881 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq9878
  have eq9893 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq9881
    | exact resolve eq9881 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9881
  have eq10013 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq9893 eq111
    | exact resolve eq111 eq9893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9893
  have eq10023 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10013
  have eq10025 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10023
       have r₂ := eq28
       grind)
    | exact resolve eq10023 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10023
  have eq10140 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10025
  have eq10152 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10140
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10140
    | exact resolve eq10140 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10140
  have eq10269 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq10152
       grind)
    | exact superpose eq10152 eq45
    | exact resolve eq45 eq10152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10152
  have eq10287 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq10269
    | exact resolve eq10269 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10269
  have eq10316 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10287 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq10287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10319 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq10316
    | exact resolve eq10316 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10316
  have eq10330 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10319
       have r₂ := eq28
       grind)
    | exact resolve eq10319 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10319
  have eq10332 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq10330
    | exact resolve eq10330 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10330
  have eq10333 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq10332
  have eq10337 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq10333
  have eq10349 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq10337
    | exact resolve eq10337 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10337
  have eq10477 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10349 eq10287
    | exact resolve eq10287 eq10349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10287 eq10349
  have eq10481 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10477
  have eq10485 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10481
       have r₂ := eq28
       grind)
    | exact resolve eq10481 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10481
  have eq10601 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10485 eq72
    | (have r₁ := eq72
       have r₂ := eq10485
       grind)
    | exact resolve eq72 eq10485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq10602 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10485 eq28
    | exact resolve eq28 eq10485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10485
  have eq10603 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq10601
  have eq10725 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10603 eq111
    | exact resolve eq111 eq10603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10743 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq10725
  have eq10757 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10743
       have r₂ := eq10602
       grind)
    | exact resolve eq10743 eq10602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10743
  have eq10764 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq10757
  have eq10776 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq10764
    | exact resolve eq10764 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10764
  have eq10865 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10776 eq111
    | exact resolve eq111 eq10776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq10776
  have eq10879 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq10865
  have eq10883 : y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10879
       have r₂ := eq28
       grind)
    | exact resolve eq10879 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10879
  have eq10887 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by grind
  clear eq10883
  have eq10899 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10887
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10887
    | exact resolve eq10887 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10887
  have eq10906 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq10899
       grind)
    | exact superpose eq10899 eq45
    | exact resolve eq45 eq10899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10899
  have eq10924 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq10906
    | exact resolve eq10906 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10906
  have eq10946 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10924 eq10603
    | exact resolve eq10603 eq10924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10603
  have eq10952 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq10946
  have eq10960 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10952
       have r₂ := eq10602
       grind)
    | exact resolve eq10952 eq10602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10602 eq10952
  have eq10978 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq10960
  have eq10990 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq10978
    | exact resolve eq10978 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10978
  have eq11012 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10990 eq10924
    | exact resolve eq10924 eq10990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10924 eq10990
  have eq11016 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11012
  have eq11024 : y = (M.op x y) := by
    first
    | (have r₁ := eq11016
       have r₂ := eq28
       grind)
    | exact resolve eq11016 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11016
  have eq11026 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq11024 eq21
    | exact resolve eq21 eq11024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq11031 : y ≠ y ∨ y = (M.op x x) ∨ y = (k x y) := by
    first
    | exact superpose eq11024 eq71
    | (have r₁ := eq71
       have r₂ := eq11024
       grind)
    | exact resolve eq71 eq11024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq11080 : y = (k x y) ∨ y = (M.op x x) := by grind
  clear eq11031
  have eq11131 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq11026
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11026
    | exact resolve eq11026 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11026
  have eq11133 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq11131 eq27
    | exact resolve eq27 eq11131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq11278 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11080
       grind)
    | exact superpose eq11080 eq45
    | exact resolve eq45 eq11080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11288 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq626 x y
       have i₂ := eq11080
       grind)
    | exact superpose eq11080 eq626
    | (have j0 := eq626 x y
       grind)
    | exact resolve eq626 eq11080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11080
  have eq11291 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq11288
  have eq11298 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11291
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11291
    | exact resolve eq11291 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11291
  have eq11306 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq11131 eq11278
    | exact resolve eq11278 eq11131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11278
  have eq11308 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq11131 eq11298
    | exact resolve eq11298 eq11131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11298
  have eq11316 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11306
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11306
    | exact resolve eq11306 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11306
  have eq11317 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11308
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11308
    | exact resolve eq11308 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11308
  have eq11323 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq11131 eq11316
    | exact resolve eq11316 eq11131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11316
  have eq11324 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq11133 eq11317
    | exact resolve eq11317 eq11133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11317
  have eq11326 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq11324
       have r₂ := eq28
       grind)
    | exact resolve eq11324 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11324
  have eq11328 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11326
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11326
    | exact resolve eq11326 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11326
  have eq11330 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11328
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11328
    | exact resolve eq11328 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11328
  have eq11332 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq11131 eq11330
    | exact resolve eq11330 eq11131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11330
  have eq11394 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by grind
  clear eq11332
  have eq11410 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq11133 eq11394
    | exact resolve eq11394 eq11133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11394
  have eq11428 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq11410 eq11323
    | exact resolve eq11323 eq11410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11323 eq11410
  have eq11432 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq11428
  have eq11434 : y = (M.op x x) := by
    first
    | (have r₁ := eq11432
       have r₂ := eq28
       grind)
    | exact resolve eq11432 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11432
  have eq11453 : (M.op x y) = (k x y) := by grind
  clear eq11434
  have eq11465 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq11453
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11453
    | exact resolve eq11453 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq11453
  have eq11467 : y = (k x y) := by
    first
    | exact superpose eq11024 eq11465
    | exact resolve eq11465 eq11024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11024 eq11465
  have eq11480 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11467
       grind)
    | exact superpose eq11467 eq45
    | exact resolve eq45 eq11467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq11490 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq626 x y
       have i₂ := eq11467
       grind)
    | exact superpose eq11467 eq626
    | (have j0 := eq626 x y
       grind)
    | exact resolve eq626 eq11467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626 eq11467
  have eq11493 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq11490
  have eq11499 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11493
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11493
    | exact resolve eq11493 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11493
  have eq11507 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq11131 eq11480
    | exact resolve eq11480 eq11131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11480
  have eq11508 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11131 eq11499
    | exact resolve eq11499 eq11131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11499
  have eq11516 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq11507
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11507
    | exact resolve eq11507 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11507
  have eq11517 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11508
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11508
    | exact resolve eq11508 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11508
  have eq11523 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq11131 eq11516
    | exact resolve eq11516 eq11131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11516
  have eq11524 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11133 eq11517
    | exact resolve eq11517 eq11133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11517
  have eq11526 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq11524
       have r₂ := eq28
       grind)
    | exact resolve eq11524 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11524
  have eq11528 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11526
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11526
    | exact resolve eq11526 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq11526
  have eq11530 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11528
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11528
    | exact resolve eq11528 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq11528
  have eq11532 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11131 eq11530
    | exact resolve eq11530 eq11131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11131 eq11530
  have eq11594 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq11532
  have eq11606 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq11133 eq11594
    | exact resolve eq11594 eq11133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11133 eq11594
  have eq11607 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11523 eq11606
    | exact resolve eq11606 eq11523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11523 eq11606
  have eq11608 : False := by grind
  exact eq11608

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_x_y_pxy_pxx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = X1 := by
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
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq74 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq69 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq74 (σ X0)
       grind)
    | exact superpose eq74 eq15
    | exact resolve eq15 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq77 X0
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq77
    | exact resolve eq77 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq77
  have eq104 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq107 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq104 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq104
    | exact resolve eq104 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq110 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq107
  have eq263 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq268 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq272 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq263 X0 X1
       have i₂ := eq88 X0
       grind)
    | exact superpose eq88 eq263
    | (have j0 := eq263 X0 X1
       grind)
    | exact resolve eq263 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq1811 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq268 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq268
    | exact resolve eq268 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq1880 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1811 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1811
    | (have j0 := eq1811 X0 X1
       grind)
    | exact resolve eq1811 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1811
  have eq2171 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq272 x y
       grind)
    | exact superpose eq272 eq16
    | (have j1 := eq272 x y
       grind)
    | exact resolve eq16 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq6830 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2171
       have i₂ := eq1880 y x
       grind)
    | exact superpose eq1880 eq2171
    | (have j1 := eq1880 (σ y) (σ (M.op x x))
       grind)
    | (have r₁ := eq2171
       have r₂ := eq1880 y x
       grind)
    | (have r₁ := eq2171
       have r₂ := eq1880 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2171
       have r₂ := eq1880 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2171 eq1880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1880 eq2171
  have eq6831 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq6830
  have eq6833 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6831
       grind)
    | exact superpose eq6831 eq16
    | exact resolve eq16 eq6831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6831
  have eq6834 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq6833
       have r₂ := eq88 x
       grind)
    | exact resolve eq6833 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6833
  have eq6836 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6834
       grind)
    | exact superpose eq6834 eq10
    | exact resolve eq10 eq6834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6834
  have eq6900 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6836
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6836
    | exact resolve eq6836 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6836
  have eq6903 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6900
       grind)
    | exact superpose eq6900 eq16
    | exact resolve eq16 eq6900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6900
  have eq6904 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq6903
       have r₂ := eq88 x
       grind)
    | exact resolve eq6903 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq6903
  have eq6914 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq110 x
       have i₂ := eq6904
       grind)
    | exact superpose eq6904 eq110
    | exact resolve eq110 eq6904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6904
  have eq6953 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq6914
       have r₂ := eq16
       grind)
    | exact resolve eq6914 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6914
  have eq6968 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq6953
       grind)
    | exact superpose eq6953 eq10
    | exact resolve eq10 eq6953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6953
  have eq7032 : y = (M.op x x) := by
    first
    | (have i₁ := eq6968
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq6968
    | exact resolve eq6968 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6968
  have eq7046 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq110 x
       have i₂ := eq7032
       grind)
    | exact superpose eq7032 eq110
    | exact resolve eq110 eq7032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq7032
  have eq7085 : False := by grind
  exact eq7085

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxy_pyy_pxy_pyy_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq41 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq37 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq37 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq40 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq40 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq40 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq21 X1
       grind)
    | exact superpose eq21 eq42
    | (have j0 := eq42 X0 X1
       grind)
    | exact resolve eq42 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq42
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       have j1 := eq41 X1 X0
       grind)
    | (have r₁ := eq48 X0 X0
       have r₂ := eq41 X0 X0
       grind)
    | (have r₁ := eq48 X1 X0
       have r₂ := eq41 X0 X1
       grind)
    | exact resolve eq48 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq48
  have eq152 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq159 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq152 X0 X1
       have j1 := eq50 X0 X1
       grind)
    | (have r₁ := eq152 X0 X1
       have r₂ := eq50 X0 X1
       grind)
    | (have r₁ := eq152 X0 X0
       have r₂ := eq50 X0 X0
       grind)
    | exact resolve eq152 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq152
  have eq272 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq159 (σ X0) (σ X1)
       grind)
    | exact superpose eq159 eq15
    | exact resolve eq15 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq272 X0 X1
       have i₂ := eq159 X0 X1
       grind)
    | exact superpose eq159 eq272
    | exact resolve eq272 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq272
  have eq281 : False := by grind
  exact eq281

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxy_y_pxy_pyy_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
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
  clear eq22
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
  have eq50 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq14 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq61 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq72 x y
       grind)
    | exact superpose eq72 eq44
    | (have j1 := eq72 x y
       grind)
    | exact resolve eq44 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq55
       have i₂ := eq72 sF2 sF3
       grind)
    | exact superpose eq72 eq55
    | (have j1 := eq72 (σ x) (σ y)
       grind)
    | exact resolve eq55 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq88 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq87
    | exact resolve eq87 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq83
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq83
    | exact resolve eq83 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq92 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq88
    | exact resolve eq88 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq90
    | exact resolve eq90 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq93
    | exact resolve eq93 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq97 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq94 eq72
    | (have j0 := eq72 (σ x) (σ y)
       grind)
    | exact resolve eq72 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq97
    | exact resolve eq97 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq101 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq98
       have r₂ := eq27
       grind)
    | exact resolve eq98 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq103 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq101
    | exact resolve eq101 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq105 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq103 eq27
    | exact resolve eq27 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : y ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (k x y) = (M.op y y) := by
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
  have eq107 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq123 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq119
       have i₂ := eq61 sF3
       grind)
    | exact superpose eq61 eq119
    | exact resolve eq119 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq125 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq123
       have i₂ := eq61 y
       grind)
    | exact superpose eq61 eq123
    | exact resolve eq123 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq123
  have eq459 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq50 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq50 X1 X0 X3
       grind)
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq495 : (k (σ x) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq44
    | exact resolve eq44 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq92
  have eq498 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq495
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq495
    | exact resolve eq495 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495
  have eq587 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq103 eq107
    | (have r₁ := eq107
       have r₂ := eq103
       grind)
    | exact resolve eq107 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq588 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq587
  have eq593 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq588 eq94
    | exact resolve eq94 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq596 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq593
  have eq605 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq596 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq608 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq72 (σ x) (σ y)
       grind)
    | (have r₁ := eq605
       have r₂ := eq72 (σ x) (σ y)
       grind)
    | exact resolve eq605 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq611 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq608
    | exact resolve eq608 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq698 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq611 eq94
    | exact resolve eq94 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq611
  have eq701 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq698
  have eq705 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq701
       have r₂ := eq27
       grind)
    | exact resolve eq701 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq708 : ∀ X0 X1 : G, (M.op X0 (σ (M.op x y))) = (M.op (M.op X0 (σ (M.op x y))) (M.op X1 (σ y))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq705 eq50
    | exact resolve eq50 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq710 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X1 (σ (M.op x y))))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq705 eq14
    | exact resolve eq14 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq894 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op (M.op X0 (σ (M.op x y))) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq708
    | (have j0 := eq708 X0 (σ x)
       grind)
    | exact resolve eq708 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq909 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq103 eq894
    | exact resolve eq894 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq894
  have eq914 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq909 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq948 : ∀ X0 X1 : G, (M.op X1 (σ (M.op x y))) = (M.op (M.op X1 (σ (M.op x y))) (M.op X0 (σ (M.op x y)))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq914 eq708
    | exact resolve eq708 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708 eq914
  have eq953 : ∀ X0 X1 : G, (M.op X1 (σ (M.op x y))) = (M.op (M.op X1 (σ (M.op x y))) (M.op X0 (σ (M.op x y)))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq948 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq1056 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ (M.op x y)))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq953 eq710
    | exact resolve eq710 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953
  have eq1069 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ (M.op x y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1056 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056
  have eq1075 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1069 eq710
    | exact resolve eq710 eq1069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710 eq1069
  have eq1081 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1075
  have eq1085 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1081 eq705
    | exact resolve eq705 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705 eq1081
  have eq1099 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq1085
  have eq1104 : y = (M.op x y) := by
    first
    | (have r₁ := eq1099
       have r₂ := eq105
       grind)
    | exact resolve eq1099 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq1099
  have eq1151 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1104 eq20
    | exact resolve eq20 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1153 : y ≠ y ∨ y = (M.op y x) ∨ (k x y) = (M.op y y) := by
    first
    | exact superpose eq1104 eq106
    | (have r₁ := eq106
       have r₂ := eq1104
       grind)
    | exact resolve eq106 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq1161 : y = (M.op y x) ∨ (k x y) = (M.op y y) := by grind
  clear eq1153
  have eq1169 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1151
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1151
    | exact resolve eq1151 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151
  have eq1184 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1169 eq498
    | exact resolve eq498 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq1199 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq1184
       have r₂ := eq27
       grind)
    | exact resolve eq1184 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184
  have eq1229 : (k x (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1199 eq59
    | exact resolve eq59 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq1199
  have eq1231 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1104 eq1229
    | exact resolve eq1229 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229
  have eq1468 : (τ (M.op (σ x) (σ y))) = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1161
       have i₂ := eq1231
       grind)
    | exact superpose eq1231 eq1161
    | exact resolve eq1161 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161
  have eq1473 : (M.op (σ y) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq125
       have i₂ := eq1468
       grind)
    | exact superpose eq1468 eq125
    | exact resolve eq125 eq1468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468
  have eq1488 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1473
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq1473
    | exact resolve eq1473 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq1491 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1169 eq1488
    | exact resolve eq1488 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488
  have eq7885 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) (M.op x y))) = (M.op (M.op X0 (M.op (M.op x y) (M.op x y))) (M.op X1 (M.op y y))) := by
    intro X0 X1
    first
    | (have i₁ := eq459 X1 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq459
    | (have j0 := eq459 X1 y X0 x
       grind)
    | exact resolve eq459 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq7949 : ∀ X0 X1 : G, (M.op X0 (M.op y y)) = (M.op (M.op X0 (M.op y y)) (M.op X1 (M.op y y))) := by
    intro X0 X1
    first
    | exact superpose eq1104 eq7885
    | exact resolve eq7885 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7885
  have eq12882 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq14 y (M.op X0 (M.op y y)) x
       have i₂ := eq7949 X0 x
       grind)
    | exact superpose eq7949 eq14
    | exact resolve eq14 eq7949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7949
  have eq12946 : y = (M.op y y) := by
    first
    | (have i₁ := eq14 y y x
       have i₂ := eq12882 x
       grind)
    | exact superpose eq12882 eq14
    | exact resolve eq14 eq12882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12882
  have eq12977 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq125
       have i₂ := eq12946
       grind)
    | exact superpose eq12946 eq125
    | exact resolve eq125 eq12946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq12946
  have eq13032 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1169 eq12977
    | exact resolve eq12977 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12977
  have eq13040 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq13032
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13032
    | exact resolve eq13032 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13032
  have eq13044 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1169 eq13040
    | exact resolve eq13040 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13040
  have eq13049 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq13044 eq1491
    | exact resolve eq1491 eq13044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1491 eq13044
  have eq13111 : y = (M.op y x) := by
    first
    | (have r₁ := eq13049
       have r₂ := eq27
       grind)
    | exact resolve eq13049 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13049
  have eq13390 : y ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq13111
       grind)
    | exact superpose eq13111 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq13111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13111
  have eq13396 : (M.op x y) = (k x y) := by
    first
    | (have j1 := eq72 x y
       grind)
    | (have r₁ := eq13390
       have r₂ := eq72 x y
       grind)
    | exact resolve eq13390 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq13390
  have eq13400 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13396
       have i₂ := eq1231
       grind)
    | exact superpose eq1231 eq13396
    | exact resolve eq13396 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231 eq13396
  have eq13403 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13400
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13400
    | exact resolve eq13400 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq13400
  have eq13404 : y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1104 eq13403
    | exact resolve eq13403 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104 eq13403
  have eq13429 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13404 eq15
    | exact resolve eq15 eq13404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13404
  have eq13506 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13429
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13429
    | exact resolve eq13429 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq13429
  have eq13547 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1169 eq13506
    | exact resolve eq13506 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169 eq13506
  have eq13575 : False := by grind
  exact eq13575

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(Y,X) else if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_x_y_pyx_pyx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq68 (σ X0)
       grind)
    | exact superpose eq68 eq15
    | exact resolve eq15 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq71
    | exact resolve eq71 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq71
  have eq558 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq608 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq561 x y
       grind)
    | exact superpose eq561 eq16
    | (have j1 := eq561 x y
       grind)
    | exact resolve eq16 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq615 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq561 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2904 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq558 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq558
    | exact resolve eq558 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq2955 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2904 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2904
    | (have j0 := eq2904 X0 X1
       grind)
    | exact resolve eq2904 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2904
  have eq10642 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq608
       have i₂ := eq2955 y x
       grind)
    | exact superpose eq2955 eq608
    | (have j1 := eq2955 (σ x) (σ y)
       grind)
    | (have r₁ := eq608
       have r₂ := eq2955 y x
       grind)
    | (have r₁ := eq608
       have r₂ := eq2955 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq608
       have r₂ := eq2955 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq608 eq2955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2955
  have eq10643 : x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq10642
  have eq17398 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq615 X1 X0
       have i₂ := eq561 X0 X1
       grind)
    | exact superpose eq561 eq615
    | (have j0 := eq615 X0 X1
       have j1 := eq561 X0 X1
       grind)
    | (have r₁ := eq615 X0 X0
       have r₂ := eq561 X0 X0
       grind)
    | exact resolve eq615 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq17403 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq17398 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17398
  have eq17407 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq17403 X0 X1
       have j1 := eq615 X0 X1
       grind)
    | (have r₁ := eq17403 X0 X1
       have r₂ := eq615 (k X0 X1) (k X1 X0)
       grind)
    | (have r₁ := eq17403 X0 X1
       have r₂ := eq615 (k X1 X0) (k X0 X1)
       grind)
    | (have r₁ := eq17403 X0 X1
       have r₂ := eq615 X0 X1
       grind)
    | exact resolve eq17403 eq615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615 eq17403
  have eq19924 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17407 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq17407
    | (have j0 := eq17407 (τ X0) (τ X1)
       grind)
    | exact resolve eq17407 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq17407
  have eq19983 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (k (σ (τ X1)) X0) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq19924 X0 X1
       have i₂ := eq19 X0 (τ X1)
       grind)
    | exact superpose eq19 eq19924
    | (have j0 := eq19924 X0 X1
       grind)
    | exact resolve eq19924 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq19924
  have eq20041 : ∀ X0 X1 : G, (k X1 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq19983 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq19983
    | (have j0 := eq19983 X0 X1
       grind)
    | exact resolve eq19983 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19983
  have eq20091 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq20041 X1 X0
       have i₂ := eq11 (k X1 X0)
       grind)
    | exact superpose eq11 eq20041
    | (have j0 := eq20041 X0 X1
       grind)
    | (have r₁ := eq20041 X1 X1
       have r₂ := eq11 (k X1 X1)
       grind)
    | exact resolve eq20041 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20041
  have eq20139 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ (k X1 X0) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq20091 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq20091
    | (have j0 := eq20091 X0 X1
       grind)
    | exact resolve eq20091 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20091
  have eq20184 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ (k X1 X0) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq20139 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20139
    | (have j0 := eq20139 X0 X1
       grind)
    | exact resolve eq20139 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20139
  have eq20214 : ∀ X0 X1 : G, (M.op X0 (σ (τ X1))) = (M.op (σ (τ X1)) X0) ∨ X0 = X1 ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20184 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20184
    | (have j0 := eq20184 X0 X1
       grind)
    | exact resolve eq20184 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20184
  have eq20232 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20214 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20214
    | (have j0 := eq20214 X0 X1
       grind)
    | exact resolve eq20214 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20214
  have eq41075 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10643
       grind)
    | exact superpose eq10643 eq16
    | exact resolve eq16 eq10643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10643
  have eq41076 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq41075
       have r₂ := eq82 x
       grind)
    | exact resolve eq41075 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41075
  have eq41078 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq41076
       grind)
    | exact superpose eq41076 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq41076
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq41076
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq41076
       grind)
    | exact resolve eq12 eq41076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41076
  have eq41129 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq41078
  have eq41131 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq608
       have i₂ := eq41129
       grind)
    | exact superpose eq41129 eq608
    | exact resolve eq608 eq41129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608 eq41129
  have eq41135 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq41131
  have eq41136 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq41135
  have eq41149 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq41136
       grind)
    | exact superpose eq41136 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq41136
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq41136
       grind)
    | exact resolve eq12 eq41136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41150 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq41136
       grind)
    | exact superpose eq41136 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq41136
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq41136
       grind)
    | exact resolve eq12 eq41136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41136
  have eq41201 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq41150
  have eq41202 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq41149
  have eq41208 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq41201
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq41201
    | exact resolve eq41201 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41201
  have eq41209 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq41202
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq41202
    | exact resolve eq41202 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41202
  have eq41213 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41208
       grind)
    | exact superpose eq41208 eq16
    | exact resolve eq16 eq41208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41315 : (σ (k x y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq41208
       have i₂ := eq41209
       grind)
    | exact superpose eq41209 eq41208
    | exact resolve eq41208 eq41209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41208 eq41209
  have eq41391 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (k y x)) := by grind
  clear eq41315
  have eq41412 : y = (τ (σ x)) ∨ (σ (k x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq41391
       grind)
    | exact superpose eq41391 eq10
    | exact resolve eq10 eq41391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41391
  have eq41605 : x = y ∨ (σ (k x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq41412
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq41412
    | exact resolve eq41412 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41412
  have eq41607 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41605
       grind)
    | exact superpose eq41605 eq16
    | exact resolve eq16 eq41605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41605
  have eq41608 : (σ (k x y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq41607
       have r₂ := eq82 x
       grind)
    | exact resolve eq41607 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41607
  have eq41621 : (k y x) = (τ (σ (k x y))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq41608
       grind)
    | exact superpose eq41608 eq10
    | exact resolve eq10 eq41608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41608
  have eq41816 : (k x y) = (k y x) := by
    first
    | (have i₁ := eq41621
       have i₂ := eq10 (k x y)
       grind)
    | exact superpose eq10 eq41621
    | exact resolve eq41621 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41621
  have eq41846 : (k x y) ≠ (k x y) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq20232 x y
       have i₂ := eq41816
       grind)
    | exact superpose eq41816 eq20232
    | (have j0 := eq20232 x y
       grind)
    | (have r₁ := eq20232 x y
       have r₂ := eq41816
       grind)
    | (have r₁ := eq20232 y x
       have r₂ := eq41816
       grind)
    | exact resolve eq20232 eq41816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20232 eq41816
  have eq41860 : x = y ∨ (M.op x y) = (M.op y x) := by grind
  clear eq41846
  have eq41867 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41860
       grind)
    | exact superpose eq41860 eq16
    | exact resolve eq16 eq41860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41860
  have eq41868 : (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq41867
       have r₂ := eq82 x
       grind)
    | exact resolve eq41867 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41867
  have eq42206 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq41868
       grind)
    | exact superpose eq41868 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq41868
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq41868
       grind)
    | exact resolve eq12 eq41868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41868
  have eq42257 : (M.op x y) = (k x y) := by grind
  clear eq42206
  have eq42262 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq41213
       have i₂ := eq42257
       grind)
    | exact superpose eq42257 eq41213
    | exact resolve eq41213 eq42257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41213 eq42257
  have eq42269 : (σ x) = (σ y) := by grind
  clear eq42262
  have eq42270 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq42269
       grind)
    | exact superpose eq42269 eq16
    | exact resolve eq16 eq42269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42271 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq42269
       grind)
    | exact superpose eq42269 eq10
    | exact resolve eq10 eq42269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42269
  have eq42464 : x = y := by
    first
    | (have i₁ := eq42271
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq42271
    | exact resolve eq42271 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42271
  have eq42465 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq42270
       have i₂ := eq82 x
       grind)
    | exact superpose eq82 eq42270
    | exact resolve eq42270 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq42270
  have eq42466 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq42465
       have i₂ := eq42464
       grind)
    | exact superpose eq42464 eq42465
    | exact resolve eq42465 eq42464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42464 eq42465
  have eq42467 : False := by grind
  exact eq42467

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pxy_pxy_pxx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
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
  have eq28 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq28 (σ X0)
       grind)
    | exact superpose eq28 eq15
    | exact resolve eq15 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq28 (τ X0)
       grind)
    | exact superpose eq28 eq17
    | exact resolve eq17 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq32 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32
    | exact resolve eq32 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq31
    | exact resolve eq31 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq33
    | exact resolve eq33 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq33
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq76 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 X1
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq72
    | (have j0 := eq72 X0 X1
       grind)
    | exact resolve eq72 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 X1
       have i₂ := eq34 X1
       grind)
    | exact superpose eq34 eq76
    | (have j0 := eq76 X0 X1
       grind)
    | exact resolve eq76 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq84 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq79
    | exact resolve eq79 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq194 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq157 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq157
    | (have j0 := eq157 X0 X1
       grind)
    | exact resolve eq157 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq157
  have eq198 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq194 X0 X1
       have j1 := eq86 X1 X0
       grind)
    | (have r₁ := eq194 X1 (τ X1)
       have r₂ := eq86 (τ X1) X1
       grind)
    | (have r₁ := eq194 X1 X0
       have r₂ := eq86 X0 X1
       grind)
    | exact resolve eq194 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq202 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq198 X0 X1
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq198
    | (have j0 := eq198 X0 X1
       grind)
    | exact resolve eq198 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq198
  have eq518 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq202 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq202
    | exact resolve eq202 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq531 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq202 (σ X0) X1
       grind)
    | exact superpose eq202 eq15
    | (have j1 := eq202 (σ X0) X1
       grind)
    | exact resolve eq15 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq542 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq531 X0 X1
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq531
    | (have j0 := eq531 X0 X1
       grind)
    | exact resolve eq531 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq558 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq518 (τ X1) X0
       grind)
    | exact superpose eq518 eq18
    | (have j1 := eq518 (τ X1) X0
       grind)
    | exact resolve eq18 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq518
  have eq1995 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq558 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq558
    | exact resolve eq558 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq2056 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1995 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1995
    | (have j0 := eq1995 X0 X1
       grind)
    | exact resolve eq1995 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1995
  have eq7464 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq542 x y
       grind)
    | exact superpose eq542 eq16
    | (have j1 := eq542 x y
       grind)
    | exact resolve eq16 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7541 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq542 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq7747 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq7464
       have i₂ := eq2056 y x
       grind)
    | exact superpose eq2056 eq7464
    | (have j1 := eq2056 y x
       grind)
    | (have r₁ := eq7464
       have r₂ := eq2056 y x
       grind)
    | exact resolve eq7464 eq2056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7464
  have eq7748 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq7747
  have eq7751 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq7748
       grind)
    | exact superpose eq7748 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq7748
       grind)
    | exact resolve eq13 eq7748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7771 : (k x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq7751
  have eq964537 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq7541 x y
       have i₂ := eq7771
       grind)
    | exact superpose eq7771 eq7541
    | (have j0 := eq7541 x y
       grind)
    | exact resolve eq7541 eq7771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7771
  have eq964589 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq964537
  have eq964590 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq964589
  have eq967909 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq964590
       grind)
    | exact superpose eq964590 eq16
    | exact resolve eq16 eq964590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq967910 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq84 x (σ y)
       have i₂ := eq964590
       grind)
    | exact superpose eq964590 eq84
    | (have j0 := eq84 x (σ y)
       grind)
    | (have r₁ := eq84 x (σ y)
       have r₂ := eq964590
       grind)
    | exact resolve eq84 eq964590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq967912 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq86 y (σ x)
       have i₂ := eq964590
       grind)
    | exact superpose eq964590 eq86
    | exact resolve eq86 eq964590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964590
  have eq968063 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq967910
  have eq968115 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq967912
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq967912
    | exact resolve eq967912 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967912
  have eq968116 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq968063
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq968063
    | exact resolve eq968063 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968063
  have eq968149 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq968116
       have i₂ := eq34 y
       grind)
    | exact superpose eq34 eq968116
    | exact resolve eq968116 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq968116
  have eq968170 : (σ (k x y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have r₁ := eq968149
       have r₂ := eq968115
       grind)
    | exact resolve eq968149 eq968115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968115 eq968149
  have eq971368 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq2056 y x
       have i₂ := eq968170
       grind)
    | exact superpose eq968170 eq2056
    | (have j0 := eq2056 y x
       grind)
    | exact resolve eq2056 eq968170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968170
  have eq971957 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have r₁ := eq971368
       have r₂ := eq967909
       grind)
    | exact resolve eq971368 eq967909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971368
  have eq975085 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq967909
       have i₂ := eq971957
       grind)
    | exact superpose eq971957 eq967909
    | exact resolve eq967909 eq971957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967909 eq971957
  have eq975232 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq975085
  have eq975233 : (M.op x x) = (M.op y y) := by grind
  clear eq975232
  have eq975364 : ∀ X0 : G, (M.op x x) ≠ (M.op X0 y) ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq975233
       grind)
    | exact superpose eq975233 eq12
    | (have j0 := eq12 X0 y
       grind)
    | exact resolve eq12 eq975233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq983959 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq975364 x
       have i₂ := eq7748
       grind)
    | exact superpose eq7748 eq975364
    | (have r₁ := eq975364 x
       have r₂ := eq7748
       grind)
    | exact resolve eq975364 eq7748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7748 eq975364
  have eq984000 : (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq983959
  have eq1038909 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq7541 x y
       have i₂ := eq984000
       grind)
    | exact superpose eq984000 eq7541
    | (have j0 := eq7541 x y
       grind)
    | exact resolve eq7541 eq984000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7541 eq984000
  have eq1038961 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq1038909
  have eq1038962 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq1038961
  have eq1038987 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1038962
       grind)
    | exact superpose eq1038962 eq16
    | exact resolve eq16 eq1038962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1038992 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq86 y (σ x)
       have i₂ := eq1038962
       grind)
    | exact superpose eq1038962 eq86
    | exact resolve eq86 eq1038962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq1038962
  have eq1039211 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1038992
       have i₂ := eq975233
       grind)
    | exact superpose eq975233 eq1038992
    | exact resolve eq1038992 eq975233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975233 eq1038992
  have eq1039212 : (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq1039211
  have eq1039256 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1039212
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1039212
    | exact resolve eq1039212 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039212
  have eq1043362 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2056 y x
       have i₂ := eq1039256
       grind)
    | exact superpose eq1039256 eq2056
    | (have j0 := eq2056 y x
       grind)
    | exact resolve eq2056 eq1039256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2056 eq1039256
  have eq1043951 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq1043362
       have r₂ := eq1038987
       grind)
    | exact resolve eq1043362 eq1038987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043362
  have eq1046947 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1038987
       have i₂ := eq1043951
       grind)
    | exact superpose eq1043951 eq1038987
    | exact resolve eq1038987 eq1043951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038987 eq1043951
  have eq1047098 : False := by grind
  exact eq1047098

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_x_pxy_x_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq23 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
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
  have eq24 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
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
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (M.op X1 (M.op X2 (M.op X0 X0))) (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 ∨ (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       grind)
    | (have r₁ := eq13 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 ∨ (M.op (M.op X1 (M.op X2 (M.op X0 X0))) (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq56
    | (have j0 := eq56 (σ X0) (σ X1)
       grind)
    | exact resolve eq56 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq56 X0 (τ X1)
       grind)
    | exact superpose eq56 eq18
    | (have j1 := eq56 X0 (τ X1)
       grind)
    | exact resolve eq18 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0) X0
       have i₂ := eq33 (σ X0)
       grind)
    | exact superpose eq33 eq22
    | exact resolve eq22 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq82 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq33 (τ X0)
       grind)
    | exact superpose eq33 eq18
    | exact resolve eq18 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq83 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82
    | exact resolve eq82 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq84 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq81 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq81
    | exact resolve eq81 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq91 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq83
    | exact resolve eq83 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq92 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq84
    | exact resolve eq84 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq84
  have eq95 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq91 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq91
    | exact resolve eq91 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq10
    | exact resolve eq10 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq112 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq23 X1 X0 X3
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq136 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67 x y
       grind)
    | exact superpose eq67 eq16
    | (have j1 := eq67 x y
       grind)
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq162 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq24 (σ X0)
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq24
    | exact resolve eq24 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq178 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (M.op X2 (M.op (τ X0) (τ X0)))))) ∨ (τ X0) = (M.op (M.op X1 (M.op X2 (M.op (τ X0) (τ X0)))) (M.op X1 (M.op X2 (M.op (τ X0) (τ X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (M.op X1 (M.op X2 (M.op (τ X0) (τ X0))))
       have i₂ := eq43 (τ X0) X1 X2
       grind)
    | exact superpose eq43 eq17
    | (have j1 := eq43 (τ X0) X1 X2
       grind)
    | exact resolve eq17 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq182 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (M.op X2 (M.op (τ X0) (τ X0)))))) = X0 ∨ (τ X0) = (M.op (M.op X1 (M.op X2 (M.op (τ X0) (τ X0)))) (M.op X1 (M.op X2 (M.op (τ X0) (τ X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq178 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq178
    | (have j0 := eq178 X0 X1 X2
       grind)
    | exact resolve eq178 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq336 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq73
    | exact resolve eq73 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq365 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq336 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq336
    | (have j0 := eq336 X0 X1
       grind)
    | exact resolve eq336 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq387 : ∀ X0 : G, (M.op (σ X0) (σ X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq12 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq162 X0
       grind)
    | exact superpose eq162 eq12
    | exact resolve eq12 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq389 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq387 X0
       grind)
    | (have r₁ := eq387 X0
       have r₂ := eq95 X0
       grind)
    | exact resolve eq387 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq387
  have eq397 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq389 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq389
    | exact resolve eq389 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq512 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq136
       have i₂ := eq56 x y
       grind)
    | exact superpose eq56 eq136
    | (have j1 := eq56 (σ x) (σ y)
       grind)
    | exact resolve eq136 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq513 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq512
  have eq862 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (M.op X2 (τ (M.op X0 X0)))))) = X0 ∨ (τ X0) = (M.op (M.op X1 (M.op X2 (M.op (τ X0) (τ X0)))) (M.op X1 (M.op X2 (M.op (τ X0) (τ X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq182 X0 X1 X2
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq182
    | (have j0 := eq182 X0 X1 X2
       grind)
    | exact resolve eq182 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq863 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (M.op X1 (M.op X2 (τ (M.op X0 X0)))) (M.op X1 (M.op X2 (τ (M.op X0 X0))))) ∨ (k X0 (σ (M.op X1 (M.op X2 (τ (M.op X0 X0)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq862 X0 X1 X2
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq862
    | (have j0 := eq862 X0 X1 X2
       grind)
    | exact resolve eq862 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq862
  have eq891 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (σ (k (τ X0) (M.op X1 (M.op X2 (τ (M.op X0 X0)))))) ∨ (k X0 (σ (M.op X1 (M.op X2 (τ (M.op X0 X0)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq397 (M.op X1 (M.op X2 (τ (M.op X0 X0))))
       have i₂ := eq863 X0 X1 X2
       grind)
    | exact superpose eq863 eq397
    | (have j1 := eq863 X0 X1 X2
       grind)
    | exact resolve eq397 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397 eq863
  have eq897 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (M.op X2 (τ (M.op X0 X0)))))) ∨ (k X0 (σ (M.op X1 (M.op X2 (τ (M.op X0 X0)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq891 X0 X1 X2
       have i₂ := eq17 X0 (M.op X1 (M.op X2 (τ (M.op X0 X0))))
       grind)
    | exact superpose eq17 eq891
    | (have j0 := eq891 X0 X1 X2
       grind)
    | exact resolve eq891 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq891
  have eq906 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (M.op X2 (τ (M.op X0 X0)))))) = X0 ∨ (k X0 (σ (M.op X1 (M.op X2 (τ (M.op X0 X0)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq897 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq897
    | (have j0 := eq897 X0 X1 X2
       grind)
    | exact resolve eq897 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq907 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (M.op X2 (τ (M.op X0 X0)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq906 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq987 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op X1 (M.op X2 (τ (M.op (σ X0) (σ X0)))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 (σ (M.op X1 (M.op X2 (τ (M.op (σ X0) (σ X0))))))
       have i₂ := eq907 (σ X0) X1 X2
       grind)
    | exact superpose eq907 eq30
    | exact resolve eq30 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq907
  have eq996 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (M.op X1 (M.op X2 (τ (M.op (σ X0) (σ X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq987 X0 X1 X2
       have i₂ := eq10 (M.op X1 (M.op X2 (τ (M.op (σ X0) (σ X0)))))
       grind)
    | exact superpose eq10 eq987
    | exact resolve eq987 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq1011 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq996 X0 X1 X2
       have i₂ := eq92 X0
       grind)
    | exact superpose eq92 eq996
    | exact resolve eq996 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq996
  have eq1020 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1011 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1011
    | exact resolve eq1011 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq1216 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1020 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq112 x X2 X0 X1
       grind)
    | exact superpose eq112 eq1020
    | exact resolve eq1020 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq1381 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X0) (M.op X2 X0)))) = X0 ∨ (M.op X0 (M.op X1 (M.op (M.op X2 X0) (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X0 (M.op X1 (M.op (M.op X2 X0) (M.op X2 X0)))
       have i₂ := eq1216 X1 X2 X0
       grind)
    | exact superpose eq1216 eq56
    | (have j0 := eq56 X0 (M.op X1 (M.op (M.op X2 X0) (M.op X2 X0)))
       grind)
    | exact resolve eq56 eq1216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq1216
  have eq1388 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X0) (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq1381 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381
  have eq1656 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1020 (M.op X1 X0) X0 x
       have i₂ := eq1388 X0 x X1
       grind)
    | exact superpose eq1388 eq1020
    | exact resolve eq1020 eq1388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020 eq1388
  have eq1859 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq145 (M.op X0 X1) X1
       have i₂ := eq1656 X1 X0
       grind)
    | exact superpose eq1656 eq145
    | (have j0 := eq145 (M.op X0 X1) X1
       grind)
    | exact resolve eq145 eq1656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq1869 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1859 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1859
  have eq2005 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1869 x y
       have i₂ := eq513
       grind)
    | exact superpose eq513 eq1869
    | exact resolve eq1869 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513 eq1869
  have eq2033 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2005
  have eq2116 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2033
       grind)
    | exact superpose eq2033 eq16
    | exact resolve eq16 eq2033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2127 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1656 (σ y) (σ x)
       have i₂ := eq2033
       grind)
    | exact superpose eq2033 eq1656
    | exact resolve eq1656 eq2033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1656 eq2033
  have eq2130 : (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq2127
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq2127
    | exact resolve eq2127 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2127
  have eq2201 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq365 y x
       have i₂ := eq2130
       grind)
    | exact superpose eq2130 eq365
    | (have j0 := eq365 y x
       grind)
    | exact resolve eq365 eq2130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365 eq2130
  have eq2249 : x = (M.op x y) := by
    first
    | (have r₁ := eq2201
       have r₂ := eq2116
       grind)
    | exact resolve eq2201 eq2116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2201
  have eq2327 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2116
       have i₂ := eq2249
       grind)
    | exact superpose eq2249 eq2116
    | exact resolve eq2116 eq2249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2116 eq2249
  have eq2339 : False := by grind
  exact eq2339

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_y_pxy_pyy_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq19 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
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
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq28 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq28 (σ X0)
       grind)
    | exact superpose eq28 eq15
    | exact resolve eq15 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq28 (τ X0)
       grind)
    | exact superpose eq28 eq17
    | exact resolve eq17 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq32 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32
    | exact resolve eq32 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq31
    | exact resolve eq31 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq33
    | exact resolve eq33 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq33
  have eq45 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq51 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 X1
       have i₂ := eq34 X1
       grind)
    | exact superpose eq34 eq71
    | (have j0 := eq71 X0 X1
       grind)
    | exact resolve eq71 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq82 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq95 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq10
    | exact resolve eq10 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq106 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq19 X1 X0 X3
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq150 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq75
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq176 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq150 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq150
    | (have j0 := eq150 X0 X1
       grind)
    | exact resolve eq150 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq180 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq176 X0 X1
       have j1 := eq82 X1 X0
       grind)
    | (have r₁ := eq176 X1 X0
       have r₂ := eq82 X0 X1
       grind)
    | exact resolve eq176 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq176
  have eq489 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq180 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq180
    | exact resolve eq180 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq180 (σ X0) X1
       grind)
    | exact superpose eq180 eq15
    | (have j1 := eq180 (σ X0) X1
       grind)
    | exact resolve eq15 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq523 : ∀ X0 X1 : G, (τ X1) = (M.op X0 (τ X1)) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq489 (τ X1) X0
       grind)
    | exact superpose eq489 eq18
    | (have j1 := eq489 (τ X1) X0
       grind)
    | exact resolve eq18 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq532 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq489 X1 (τ X0)
       grind)
    | exact superpose eq489 eq17
    | (have j1 := eq489 X1 (τ X0)
       grind)
    | exact resolve eq17 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq784 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq106 x X2 X0 X1
       grind)
    | exact superpose eq106 eq9
    | exact resolve eq9 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq817 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq784 x X1 X0
       grind)
    | exact superpose eq784 eq9
    | exact resolve eq9 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq1187 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq532 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq532
    | exact resolve eq532 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq1257 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1187 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1187
    | (have j0 := eq1187 X0 X1
       grind)
    | exact resolve eq1187 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq1742 : ∀ X0 X1 : G, (τ X0) ≠ (M.op (τ X0) (τ X0)) ∨ (τ X0) = (k X1 (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (τ X1)
       have i₂ := eq523 X0 X1
       grind)
    | exact superpose eq523 eq12
    | (have j1 := eq523 X1 X0
       grind)
    | exact resolve eq12 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1748 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq817 (τ X1) X0
       have i₂ := eq523 X0 X1
       grind)
    | exact superpose eq523 eq817
    | (have j1 := eq523 (τ X0) X0
       grind)
    | exact resolve eq817 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523 eq817
  have eq1766 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1748 X0 X1
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq1748
    | (have j0 := eq1748 X0 X1
       grind)
    | exact resolve eq1748 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1748
  have eq1772 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (k X1 (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1742 X0 X1
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq1742
    | (have j0 := eq1742 X0 X1
       grind)
    | exact resolve eq1742 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq1742
  have eq1806 : ∀ X0 X1 : G, (τ X0) = (k X1 (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq1772 X0 X1
       have j1 := eq1766 X0 X1
       grind)
    | (have r₁ := eq1772 X0 X1
       have r₂ := eq1766 X0 X1
       grind)
    | exact resolve eq1772 eq1766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1766 eq1772
  have eq3614 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 (σ (τ X0))) ∨ (σ (M.op (τ X1) (τ X0))) = (k (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq1806 X0 (τ X1)
       grind)
    | exact superpose eq1806 eq17
    | (have j1 := eq1806 X0 (τ X1)
       grind)
    | exact resolve eq17 eq1806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1806
  have eq3623 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ (M.op (τ X1) (τ X0))) = (k (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3614 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3614
    | (have j0 := eq3614 X0 X1
       grind)
    | exact resolve eq3614 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3614
  have eq3638 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3623 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3623
    | (have j0 := eq3623 X0 X1
       grind)
    | exact resolve eq3623 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3623
  have eq3771 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (σ (M.op (τ (σ X0)) (τ (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3638 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3638
    | exact resolve eq3638 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3782 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq489 X0 X1
       have i₂ := eq3638 X0 X1
       grind)
    | exact superpose eq3638 eq489
    | (have j0 := eq489 X0 X1
       have j1 := eq3638 X0 X1
       grind)
    | exact resolve eq489 eq3638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489 eq3638
  have eq3822 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3782 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3782
  have eq3858 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op (τ (σ X0)) X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3771 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3771
    | (have j0 := eq3771 X0 X1
       grind)
    | exact resolve eq3771 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3771
  have eq3878 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3858 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3858
    | (have j0 := eq3858 X0 X1
       grind)
    | exact resolve eq3858 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3858
  have eq3939 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X1))
       have i₂ := eq3822 X1 X0
       grind)
    | exact superpose eq3822 eq10
    | (have j1 := eq3822 X1 X0
       grind)
    | exact resolve eq10 eq3822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3822
  have eq4097 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq502 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq4184 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4097 (τ X0) (τ X1)
       have i₂ := eq51 X1 X0
       grind)
    | exact superpose eq51 eq4097
    | (have j0 := eq4097 (τ X0) (τ X1)
       grind)
    | exact resolve eq4097 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq4196 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4184 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq4184
    | (have j0 := eq4184 X0 X1
       grind)
    | exact resolve eq4184 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4184
  have eq4202 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4196 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq4196
    | (have j0 := eq4196 X0 X1
       grind)
    | exact resolve eq4196 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4196
  have eq4204 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4202 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4202
    | (have j0 := eq4202 X0 X1
       grind)
    | exact resolve eq4202 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4202
  have eq4205 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4204 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4204
    | (have j0 := eq4204 X0 X1
       grind)
    | exact resolve eq4204 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4204
  have eq4804 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op X0 (τ X1)) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3939 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3939
    | (have j0 := eq3939 (σ X0) X1
       grind)
    | exact resolve eq3939 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3939
  have eq4944 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4804 X0 X1
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq4804
    | (have j0 := eq4804 X0 X1
       grind)
    | exact resolve eq4804 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4804
  have eq5303 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (M.op X0 (τ X1))) ∨ (σ (τ X1)) = (M.op (σ X0) (σ (τ X1))) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4097 X0 (τ X1)
       have i₂ := eq4944 X0 X1
       grind)
    | exact superpose eq4944 eq4097
    | (have j0 := eq4097 X0 (τ X1)
       have j1 := eq4944 X0 (σ (τ X1))
       grind)
    | exact resolve eq4097 eq4944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4097 eq4944
  have eq5323 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ X0) (σ (τ X1))) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5303 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5303
    | (have j0 := eq5303 X0 X1
       grind)
    | exact resolve eq5303 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5303
  have eq5330 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (σ (M.op X0 (τ X1))) ≠ X1 ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5323 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5323
    | (have j0 := eq5323 X0 X1
       grind)
    | exact resolve eq5323 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5323
  have eq5331 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) ≠ X1 ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5330 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5330
  have eq5341 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5331 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5331
    | (have j0 := eq5331 X1 (σ X0)
       grind)
    | exact resolve eq5331 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5331
  have eq6458 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq3878 X0 X1
       grind)
    | exact superpose eq3878 eq10
    | (have j1 := eq3878 X0 X1
       grind)
    | exact resolve eq10 eq3878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3878
  have eq6523 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6458 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq6458
    | (have j0 := eq6458 X0 X1
       grind)
    | exact resolve eq6458 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6458
  have eq6950 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq6523 X1 X0
       grind)
    | exact superpose eq6523 eq10
    | (have j1 := eq6523 X1 X0
       grind)
    | exact resolve eq10 eq6523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6523
  have eq7015 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6950 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6950
    | (have j0 := eq6950 X0 X1
       grind)
    | exact resolve eq6950 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6950
  have eq7068 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq7015 X1 (σ X0)
       grind)
    | exact superpose eq7015 eq45
    | (have j1 := eq7015 X1 (σ X0)
       grind)
    | exact resolve eq45 eq7015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq7015
  have eq10054 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X1) X0
       have i₂ := eq7068 X1 (σ X0)
       grind)
    | exact superpose eq7068 eq26
    | (have j1 := eq7068 X1 (σ X0)
       grind)
    | exact resolve eq26 eq7068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq7068
  have eq10111 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10054 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq10054
    | (have j0 := eq10054 X0 X1
       grind)
    | exact resolve eq10054 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10054
  have eq10142 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10111 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10111
    | (have j0 := eq10111 X0 X1
       grind)
    | exact resolve eq10111 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10111
  have eq10151 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10142 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10142
    | (have j0 := eq10142 X0 X1
       grind)
    | exact resolve eq10142 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10142
  have eq10464 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X1 X0) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4205 X1 X0
       have i₂ := eq10151 X0 X1
       grind)
    | exact superpose eq10151 eq4205
    | (have j0 := eq4205 X1 X0
       have j1 := eq10151 X0 X1
       grind)
    | (have r₁ := eq4205 X1 X0
       have r₂ := eq10151 X0 X1
       grind)
    | exact resolve eq4205 eq10151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4205 eq10151
  have eq10542 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq10464 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10464
  have eq10751 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq10542 X1 X0
       grind)
    | exact superpose eq10542 eq11
    | (have j1 := eq10542 X1 X0
       grind)
    | exact resolve eq11 eq10542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10542
  have eq11423 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10751 x y
       grind)
    | exact superpose eq10751 eq16
    | (have j1 := eq10751 x y
       grind)
    | exact resolve eq16 eq10751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10751
  have eq11527 : y = (M.op x y) := by
    first
    | (have j1 := eq1257 x y
       grind)
    | (have r₁ := eq11423
       have r₂ := eq1257 x y
       grind)
    | exact resolve eq11423 eq1257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257 eq11423
  have eq11657 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5341 y x
       have i₂ := eq11527
       grind)
    | exact superpose eq11527 eq5341
    | (have j0 := eq5341 y x
       grind)
    | exact resolve eq5341 eq11527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5341
  have eq11666 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11657
  have eq12050 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11666
       grind)
    | exact superpose eq11666 eq16
    | exact resolve eq16 eq11666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11666
  have eq12089 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq12050
       have i₂ := eq11527
       grind)
    | exact superpose eq11527 eq12050
    | exact resolve eq12050 eq11527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11527 eq12050
  have eq12090 : False := by grind
  exact eq12090
