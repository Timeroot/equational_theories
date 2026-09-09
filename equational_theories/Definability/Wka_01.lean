import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3254`: `x ◇ x = x ◇ (x ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_y_pxy_Equation3254 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3254 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3254.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op X0 x)
       have i₂ := eq9 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq68 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq316 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  clear eq59
  have eq736 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq10
    | (have j1 := eq67 X0 X1
       grind)
    | exact resolve eq10 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq6781 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq316 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq6783 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq6781 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6781
  have eq6784 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq6783 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6783
  have eq6942 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq6784 (σ X0)
       grind)
    | exact superpose eq6784 eq15
    | exact resolve eq15 eq6784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6961 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6942 X0
       have i₂ := eq6784 X0
       grind)
    | exact superpose eq6784 eq6942
    | exact resolve eq6942 eq6784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6784 eq6942
  have eq7980 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq7982 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq26 (σ X0)
       have i₂ := eq6961 X0
       grind)
    | exact superpose eq6961 eq26
    | exact resolve eq26 eq6961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8083 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7980 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq7980
    | exact resolve eq7980 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7980
  have eq8106 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq8083
  have eq8988 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq68 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq68
    | exact resolve eq68 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq9484 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8988 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8988
    | (have j0 := eq8988 X0 X1
       grind)
    | exact resolve eq8988 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8988
  have eq38411 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq736 X1 X0
       grind)
    | exact superpose eq736 eq10
    | (have j1 := eq736 X1 X0
       grind)
    | exact resolve eq10 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq38854 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq38411 X0 X1
       have i₂ := eq6961 X0
       grind)
    | exact superpose eq6961 eq38411
    | (have j0 := eq38411 X0 X1
       grind)
    | exact resolve eq38411 eq6961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38411
  have eq39450 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq38854 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq38854
    | (have j0 := eq38854 X0 X1
       grind)
    | exact resolve eq38854 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38854
  have eq39953 : ∀ X0 X1 : G, (τ (σ (M.op X1 X1))) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39450 X0 X1
       have i₂ := eq6961 X1
       grind)
    | exact superpose eq6961 eq39450
    | (have j0 := eq39450 X0 X1
       grind)
    | exact resolve eq39450 eq6961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6961 eq39450
  have eq40304 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39953 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq39953
    | (have j0 := eq39953 X0 X1
       grind)
    | exact resolve eq39953 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39953
  have eq173943 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq40304 y x
       grind)
    | exact superpose eq40304 eq16
    | (have j1 := eq40304 y x
       grind)
    | exact resolve eq16 eq40304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40304
  have eq174001 : x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq9484 x y
       grind)
    | (have r₁ := eq173943
       have r₂ := eq9484 x y
       grind)
    | exact resolve eq173943 eq9484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9484 eq173943
  have eq175028 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8106 y
       have i₂ := eq174001
       grind)
    | exact superpose eq174001 eq8106
    | exact resolve eq8106 eq174001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8106 eq174001
  have eq175138 : y = (M.op x x) := by
    first
    | (have r₁ := eq175028
       have r₂ := eq16
       grind)
    | exact resolve eq175028 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175028
  have eq176274 : y = (M.op x y) := by
    first
    | (have i₁ := eq26 x
       have i₂ := eq175138
       grind)
    | exact superpose eq175138 eq26
    | exact resolve eq26 eq175138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq176331 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7982 x
       have i₂ := eq175138
       grind)
    | exact superpose eq175138 eq7982
    | exact resolve eq7982 eq175138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7982 eq175138
  have eq181745 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq176331
       grind)
    | exact superpose eq176331 eq16
    | exact resolve eq16 eq176331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176331
  have eq181795 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq181745
       have i₂ := eq176274
       grind)
    | exact superpose eq176274 eq181745
    | exact resolve eq181745 eq176274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176274 eq181745
  have eq181796 : False := by grind
  exact eq181796

/-- `Equation3254`: `x ◇ x = x ◇ (x ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_x_pxy_Equation3254 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3254 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3254.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
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
  have eq9 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op X0 x)
       have i₂ := eq9 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq73 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq93 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq73 X0 (τ X1)
       grind)
    | exact superpose eq73 eq20
    | (have j1 := eq73 X0 (τ X1)
       grind)
    | exact resolve eq20 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq73 (σ X0) (σ X1)
       grind)
    | exact superpose eq73 eq15
    | (have j1 := eq73 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq73
  have eq608 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq102 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq609 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq608 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq745 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq609 (σ X0)
       grind)
    | exact superpose eq609 eq15
    | exact resolve eq15 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq752 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq745 X0
       have i₂ := eq609 X0
       grind)
    | exact superpose eq609 eq745
    | exact resolve eq745 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609 eq745
  have eq1100 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq26 (σ X0)
       have i₂ := eq752 X0
       grind)
    | exact superpose eq752 eq26
    | exact resolve eq26 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1844 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq93
    | exact resolve eq93 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq1948 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1844 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1844
    | (have j0 := eq1844 X0 X1
       grind)
    | exact resolve eq1844 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1844
  have eq3744 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq10
    | (have j1 := eq95 X0 X1
       grind)
    | exact resolve eq10 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq3881 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3744 X0 X1
       have i₂ := eq752 X0
       grind)
    | exact superpose eq752 eq3744
    | (have j0 := eq3744 X0 X1
       grind)
    | exact resolve eq3744 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752 eq3744
  have eq3983 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3881 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq3881
    | (have j0 := eq3881 X0 X1
       grind)
    | exact resolve eq3881 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3881
  have eq4220 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3983 x y
       grind)
    | exact superpose eq3983 eq16
    | (have j1 := eq3983 x y
       grind)
    | exact resolve eq16 eq3983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3983
  have eq4297 : y = (M.op x x) := by
    first
    | (have j1 := eq1948 y x
       grind)
    | (have r₁ := eq4220
       have r₂ := eq1948 y x
       grind)
    | exact resolve eq4220 eq1948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1948 eq4220
  have eq4655 : y = (M.op x y) := by
    first
    | (have i₁ := eq26 x
       have i₂ := eq4297
       grind)
    | exact superpose eq4297 eq26
    | exact resolve eq26 eq4297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq4669 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1100 x
       have i₂ := eq4297
       grind)
    | exact superpose eq4297 eq1100
    | exact resolve eq1100 eq4297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100 eq4297
  have eq5732 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4669
       grind)
    | exact superpose eq4669 eq16
    | exact resolve eq16 eq4669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4669
  have eq5749 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq5732
       have i₂ := eq4655
       grind)
    | exact superpose eq4655 eq5732
    | exact resolve eq5732 eq4655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4655 eq5732
  have eq5750 : False := by grind
  exact eq5750

/-- `Equation3317`: `x ◇ y = x ◇ (y ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,X) else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_pxx_y_pyx_Equation3317 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3317 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3317.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X0 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op X1 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 (M.op X1 X0)
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X1 X0)
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq12
    | (have j0 := eq12 X0 (M.op X1 X0)
       grind)
    | (have r₁ := eq12 X1 (M.op X1 X1)
       have r₂ := eq24 X1 X1
       grind)
    | exact resolve eq12 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op (M.op X1 X0) X0) = X0 ∨ (k (M.op X1 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X1 X0) X0
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq13
    | (have j0 := eq13 (M.op X1 X0) X0
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq24 X1 X1
       grind)
    | exact resolve eq13 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq50 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq102 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq50 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq50 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq50 X0 X1
       grind)
    | exact resolve eq13 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq50 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq50 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq50 X0 X1
       grind)
    | exact resolve eq12 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 X2 : G, (M.op (σ X1) X2) = (M.op (σ X1) (M.op X2 (σ X0))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X1) X2 (σ X0)
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq9
    | (have j1 := eq50 X0 X1
       grind)
    | exact resolve eq9 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq50 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq106 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq109 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq103 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq110 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq111 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq110 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq114 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq109 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq109
    | (have j0 := eq109 X0 X1
       grind)
    | exact resolve eq109 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq115 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq111 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq111
    | (have j0 := eq111 X0 X1
       grind)
    | exact resolve eq111 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq242 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq108 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq108
    | (have j0 := eq108 (τ X0)
       grind)
    | exact resolve eq108 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq244 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq242 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq242
    | (have j0 := eq242 X0
       grind)
    | exact resolve eq242 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq247 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq244 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq244
    | (have j0 := eq244 X0
       grind)
    | exact resolve eq244 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq554 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 ∨ (σ (k X1 (τ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq115 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq115
    | exact resolve eq115 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq583 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 ∨ (σ (k X1 (τ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq554 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq554
    | (have j0 := eq554 X0 X1
       grind)
    | exact resolve eq554 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq588 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k (σ X1) X0) = X0 ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq583 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq583
    | (have j0 := eq583 X0 X1
       grind)
    | exact resolve eq583 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq728 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq114 (τ X0) (τ X1)
       have i₂ := eq41 X0 X1
       grind)
    | exact superpose eq41 eq114
    | (have j0 := eq114 (τ X1) (τ X0)
       grind)
    | exact resolve eq114 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq748 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ (k (τ X0) X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq114 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq114
    | exact resolve eq114 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq822 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq114 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq824 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq822 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq849 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ (k (τ X0) X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq748 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq748
    | (have j0 := eq748 X0 X1
       grind)
    | exact resolve eq748 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq855 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq728 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq728
    | (have j0 := eq728 X0 X1
       grind)
    | exact resolve eq728 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq860 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq849 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq849
    | (have j0 := eq849 X0 X1
       grind)
    | exact resolve eq849 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq865 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq855 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq855
    | (have j0 := eq855 X0 X1
       grind)
    | exact resolve eq855 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq869 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq865 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq865
    | (have j0 := eq865 X0 X1
       grind)
    | exact resolve eq865 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq871 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (k X0 X1) = (M.op X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq869 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq869
    | (have j0 := eq869 X0 X1
       grind)
    | exact resolve eq869 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq872 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq871 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq871
    | (have j0 := eq871 X0 X1
       grind)
    | exact resolve eq871 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq873 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq872 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq872
    | (have j0 := eq872 X0 X1
       grind)
    | exact resolve eq872 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq874 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq873 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq873
    | (have j0 := eq873 X0 X1
       grind)
    | exact resolve eq873 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq1270 : ∀ X0 X1 X2 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X2)) ∨ (σ (k X2 X0)) = (M.op (σ X0) (σ X2)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X2) = (M.op (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq105 X0 X1 (σ X2)
       have i₂ := eq50 X0 X2
       grind)
    | exact superpose eq50 eq105
    | (have j0 := eq105 X0 X2 X2
       have j1 := eq50 X0 X2
       grind)
    | exact resolve eq105 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq2698 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq824 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq824
    | exact resolve eq824 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq2764 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2698 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq2698
    | (have j0 := eq2698 X0
       grind)
    | exact resolve eq2698 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2698
  have eq2768 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2764 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2764
    | (have j0 := eq2764 X0
       grind)
    | exact resolve eq2764 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2764
  have eq2769 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2768 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq2768 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq2768 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2768
  have eq2799 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq2769 (σ X0)
       grind)
    | exact superpose eq2769 eq15
    | exact resolve eq15 eq2769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2805 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq41 X0 X0
       have i₂ := eq2769 (τ X0)
       grind)
    | exact superpose eq2769 eq41
    | exact resolve eq41 eq2769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq2826 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2805 X0
       have i₂ := eq2769 X0
       grind)
    | exact superpose eq2769 eq2805
    | exact resolve eq2805 eq2769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2805
  have eq2832 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2799 X0
       have i₂ := eq2769 X0
       grind)
    | exact superpose eq2769 eq2799
    | exact resolve eq2799 eq2769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2769 eq2799
  have eq3329 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq24 (σ X0) (σ X0)
       have i₂ := eq2832 X0
       grind)
    | exact superpose eq2832 eq24
    | exact resolve eq24 eq2832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3333 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq26 (σ X0) (σ X0)
       have i₂ := eq2832 X0
       grind)
    | exact superpose eq2832 eq26
    | exact resolve eq26 eq2832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3360 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3333 X0
       have i₂ := eq2832 (M.op X0 X0)
       grind)
    | exact superpose eq2832 eq3333
    | exact resolve eq3333 eq2832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3333
  have eq3375 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq3360 X0
       have i₂ := eq26 X0 X0
       grind)
    | exact superpose eq26 eq3360
    | exact resolve eq3360 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq3360
  have eq10035 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq588 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq588
    | exact resolve eq588 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10138 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq588 (σ X0) X1
       grind)
    | exact superpose eq588 eq22
    | (have j1 := eq588 (σ X0) X1
       grind)
    | exact resolve eq22 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq588
  have eq10197 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10138 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq10138
    | (have j0 := eq10138 X0 X1
       grind)
    | exact resolve eq10138 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10138
  have eq10245 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10197 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10197
    | (have j0 := eq10197 X0 X1
       grind)
    | exact resolve eq10197 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10197
  have eq10266 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X0 ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10245 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10245
    | (have j0 := eq10245 X0 X1
       grind)
    | exact resolve eq10245 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10245
  have eq10316 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq10035 (τ X0) X1
       grind)
    | exact superpose eq10035 eq18
    | (have j1 := eq10035 (τ X0) X1
       grind)
    | exact resolve eq18 eq10035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq10035
  have eq12358 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 (σ X1)
       have i₂ := eq860 (σ X0) X1
       grind)
    | exact superpose eq860 eq36
    | (have j1 := eq860 (σ X0) X1
       grind)
    | exact resolve eq36 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq860
  have eq12439 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12358 X0 X1
       have i₂ := eq2832 X0
       grind)
    | exact superpose eq2832 eq12358
    | (have j0 := eq12358 X0 X1
       grind)
    | exact resolve eq12358 eq2832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12358
  have eq12546 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12439 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq12439
    | (have j0 := eq12439 X0 X1
       grind)
    | exact resolve eq12439 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12439
  have eq12609 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12546 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq12546
    | (have j0 := eq12546 X0 X1
       grind)
    | exact resolve eq12546 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12546
  have eq12642 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = (M.op X0 X0) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12609 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq12609
    | (have j0 := eq12609 X0 X1
       grind)
    | exact resolve eq12609 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12609
  have eq19249 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 (k X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X0
       have i₂ := eq874 X0 X1
       grind)
    | exact superpose eq874 eq24
    | (have j1 := eq874 X0 X1
       grind)
    | exact resolve eq24 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq175875 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10316 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10316
    | exact resolve eq10316 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10316
  have eq175953 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq175875 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq175875
    | (have j0 := eq175875 X0 X1
       grind)
    | exact resolve eq175875 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175875
  have eq205842 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10266 y x
       grind)
    | exact superpose eq10266 eq16
    | (have j1 := eq10266 y x
       grind)
    | exact resolve eq16 eq10266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10266
  have eq207736 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) ∨ (σ X0) = (M.op (σ X2) (σ X0)) ∨ (σ (k X1 X2)) = (M.op (σ X2) (σ X1)) ∨ (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) ∨ (σ X0) = (M.op (σ X2) (σ X0)) ∨ (σ X1) = (M.op (σ X2) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 X2 X0
       have i₂ := eq1270 X2 X0 X1
       grind)
    | (have i₁ := eq50 X2 X1
       have i₂ := eq1270 X0 X1 X2
       grind)
    | exact superpose eq1270 eq50
    | (have j0 := eq50 X2 X0
       have j1 := eq1270 X2 X0 X0
       grind)
    | exact resolve eq50 eq1270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1270
  have eq208707 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (M.op (σ X2) (σ X1)) ∨ (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) ∨ (σ X2) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X2) (σ X0)) ∨ (σ X1) = (M.op (σ X2) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq207736 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207736
  have eq212091 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq205842
       have i₂ := eq175953 x y
       grind)
    | exact superpose eq175953 eq205842
    | (have j1 := eq175953 x y
       grind)
    | (have r₁ := eq205842
       have r₂ := eq175953 x y
       grind)
    | exact resolve eq205842 eq175953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175953 eq205842
  have eq212093 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq212091
  have eq212094 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by grind
  clear eq212093
  have eq212611 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op X0 (σ y))) ∨ y = (k x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 (σ x) X0 (σ y)
       have i₂ := eq212094
       grind)
    | exact superpose eq212094 eq9
    | exact resolve eq9 eq212094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212612 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq212094
       grind)
    | exact superpose eq212094 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq212094
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq212094
       grind)
    | exact resolve eq12 eq212094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212642 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by grind
  clear eq212612
  have eq212661 : (σ (k x y)) = (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq212642
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq212642
    | exact resolve eq212642 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212642
  have eq212673 : (σ (k x y)) = (σ (M.op x x)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq212661
       have i₂ := eq2832 x
       grind)
    | exact superpose eq2832 eq212661
    | exact resolve eq212661 eq2832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212661
  have eq213677 : (k x y) = (τ (σ (M.op x x))) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq212673
       grind)
    | exact superpose eq212673 eq10
    | exact resolve eq10 eq212673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212673
  have eq213739 : (k x y) = (M.op x x) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq213677
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq213677
    | exact resolve eq213677 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213677
  have eq213751 : (k x y) = (M.op x x) ∨ y = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq213739
       have r₂ := eq12 x y
       grind)
    | exact resolve eq213739 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213739
  have eq214290 : y ≠ (M.op x x) ∨ y = (k x y) := by grind
  clear eq213751
  have eq227175 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ y = (M.op x y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq212611 (σ x)
       have i₂ := eq212094
       grind)
    | exact superpose eq212094 eq212611
    | exact resolve eq212611 eq212094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212611
  have eq227193 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ y = (M.op x y) := by grind
  clear eq227175
  have eq227198 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq227193
       have i₂ := eq2832 x
       grind)
    | exact superpose eq2832 eq227193
    | exact resolve eq227193 eq2832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227193
  have eq227754 : (σ y) = (σ (M.op x x)) ∨ y = (k x y) ∨ y = (M.op x y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq212094
       have i₂ := eq227198
       grind)
    | exact superpose eq227198 eq212094
    | exact resolve eq212094 eq227198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212094 eq227198
  have eq227784 : (σ y) = (σ (M.op x x)) ∨ y = (k x y) ∨ y = (M.op x y) := by grind
  clear eq227754
  have eq228331 : (M.op x x) = (τ (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq227784
       grind)
    | exact superpose eq227784 eq10
    | exact resolve eq10 eq227784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227784
  have eq228454 : y = (M.op x x) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq228331
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq228331
    | exact resolve eq228331 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228331
  have eq228466 : y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq228454
       have r₂ := eq214290
       grind)
    | exact resolve eq228454 eq214290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214290 eq228454
  have eq229068 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19249 x y
       have i₂ := eq228466
       grind)
    | exact superpose eq228466 eq19249
    | (have j0 := eq19249 y x
       grind)
    | exact resolve eq19249 eq228466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19249
  have eq229094 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq229068
  have eq455864 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k y x) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12642 y x
       grind)
    | exact superpose eq12642 eq16
    | (have j1 := eq12642 y x
       grind)
    | exact resolve eq16 eq12642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12642
  have eq508063 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (k X1 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq208707 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208707
  have eq508069 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (k X1 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq508063 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508063
  have eq508070 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq508069 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508069
  have eq508075 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq508070 X0 X1
       have i₂ := eq2832 X1
       grind)
    | exact superpose eq2832 eq508070
    | (have j0 := eq508070 X0 X1
       grind)
    | exact resolve eq508070 eq2832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508070
  have eq508078 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq508075 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq508075
    | (have j0 := eq508075 X1 (τ X0)
       grind)
    | exact resolve eq508075 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508075
  have eq508107 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq508078 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq508078
    | (have j0 := eq508078 X0 X1
       grind)
    | exact resolve eq508078 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq508078
  have eq508115 : ∀ X0 X1 : G, (σ X1) = (σ (τ (M.op X0 X0))) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq508107 X0 X1
       have i₂ := eq2826 X0
       grind)
    | exact superpose eq2826 eq508107
    | (have j0 := eq508107 X0 X1
       grind)
    | exact resolve eq508107 eq2826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2826 eq508107
  have eq508120 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq508115 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq508115
    | (have j0 := eq508115 X0 X1
       grind)
    | exact resolve eq508115 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508115
  have eq508132 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq508120 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq508120
    | exact resolve eq508120 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508120
  have eq508316 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3375 X1
       have i₂ := eq508132 X0 X1
       grind)
    | (have i₁ := eq3375 X0
       have i₂ := eq508132 (M.op X0 X0) X1
       grind)
    | exact superpose eq508132 eq3375
    | (have j1 := eq508132 X0 X1
       grind)
    | exact resolve eq3375 eq508132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508413 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 X1
       have i₂ := eq508132 X0 X1
       grind)
    | (have i₁ := eq30 X0 X1
       have i₂ := eq508132 (M.op X1 X0) X1
       grind)
    | exact superpose eq508132 eq30
    | (have j1 := eq508132 X0 X1
       grind)
    | (have r₁ := eq30 X1 X1
       have r₂ := eq508132 (M.op X1 X1) X1
       grind)
    | exact resolve eq30 eq508132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq508132
  have eq508457 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq508413 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508413
  have eq508585 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq508457 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508457
  have eq510420 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq508316 x y
       grind)
    | exact superpose eq508316 eq16
    | (have j1 := eq508316 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq508316 x y
       grind)
    | exact resolve eq16 eq508316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508316
  have eq510437 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq510420
  have eq510461 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq455864
       have i₂ := eq510437
       grind)
    | exact superpose eq510437 eq455864
    | exact resolve eq455864 eq510437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455864 eq510437
  have eq510636 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq510461
  have eq510679 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq510636
       grind)
    | exact superpose eq510636 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq510636
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq510636
       grind)
    | exact resolve eq12 eq510636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510636
  have eq510685 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq510679
  have eq510691 : (σ (k x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq510685
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq510685
    | exact resolve eq510685 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510685
  have eq510692 : (σ (k x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq510691
       have i₂ := eq2832 x
       grind)
    | exact superpose eq2832 eq510691
    | exact resolve eq510691 eq2832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2832 eq510691
  have eq510732 : (k x y) = (τ (σ (M.op x x))) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq510692
       grind)
    | exact superpose eq510692 eq10
    | exact resolve eq10 eq510692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510692
  have eq510744 : (k x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq510732
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq510732
    | exact resolve eq510732 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510732
  have eq510745 : (k x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq510744
       have r₂ := eq12 x y
       grind)
    | exact resolve eq510744 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510744
  have eq510763 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq228466
       have i₂ := eq510745
       grind)
    | exact superpose eq510745 eq228466
    | exact resolve eq228466 eq510745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228466 eq510745
  have eq510932 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq24 y y
       have i₂ := eq510763
       grind)
    | exact superpose eq510763 eq24
    | exact resolve eq24 eq510763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510763
  have eq510972 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq510932
       have i₂ := eq24 x y
       grind)
    | exact superpose eq24 eq510932
    | exact resolve eq510932 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510932
  have eq510989 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq510972
       have i₂ := eq229094
       grind)
    | exact superpose eq229094 eq510972
    | exact resolve eq510972 eq229094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq510995 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq229094
       have i₂ := eq510972
       grind)
    | exact superpose eq510972 eq229094
    | exact resolve eq229094 eq510972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229094 eq510972
  have eq511070 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq510995
  have eq511076 : x = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq510989
  have eq511182 : x ≠ x ∨ (k y x) = (M.op y y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq511076
       grind)
    | exact superpose eq511076 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq511076
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq511076
       grind)
    | exact resolve eq12 eq511076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq511184 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq24 y x
       have i₂ := eq511076
       grind)
    | exact superpose eq511076 eq24
    | exact resolve eq24 eq511076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq511193 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ x = (k x x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x y
       have i₂ := eq511076
       grind)
    | exact superpose eq511076 eq40
    | exact resolve eq40 eq511076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq511076
  have eq511259 : (k y x) = (M.op y y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq511182
  have eq511273 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq247 x
       grind)
    | (have r₁ := eq511193
       have r₂ := eq247 x
       grind)
    | exact resolve eq511193 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq511193
  have eq511275 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq511273
       have r₂ := eq511070
       grind)
    | exact resolve eq511273 eq511070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511070 eq511273
  have eq511645 : x ≠ (M.op x x) ∨ x = (k y x) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq508585 y x
       have i₂ := eq511184
       grind)
    | exact superpose eq511184 eq508585
    | (have j0 := eq508585 y x
       grind)
    | exact resolve eq508585 eq511184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508585 eq511184
  have eq511648 : x ≠ (M.op x x) ∨ x = (k y x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq511645
  have eq511666 : x = (k y x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq511648
       have r₂ := eq511275
       grind)
    | exact resolve eq511648 eq511275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511275 eq511648
  have eq511885 : x = (M.op y y) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq511666
       have i₂ := eq511259
       grind)
    | exact superpose eq511259 eq511666
    | exact resolve eq511666 eq511259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511259 eq511666
  have eq511951 : x = (M.op y y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq511885
  have eq512020 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3375 y
       have i₂ := eq511951
       grind)
    | exact superpose eq511951 eq3375
    | exact resolve eq3375 eq511951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3375 eq511951
  have eq512313 : y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq512020
       have r₂ := eq16
       grind)
    | exact resolve eq512020 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512020
  have eq512337 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op X0 y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 x X0 y
       have i₂ := eq512313
       grind)
    | exact superpose eq512313 eq9
    | exact resolve eq9 eq512313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513561 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq512337 x
       have i₂ := eq512313
       grind)
    | exact superpose eq512313 eq512337
    | exact resolve eq512337 eq512313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512337
  have eq513624 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq513561
  have eq513659 : y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq512313
       have i₂ := eq513624
       grind)
    | exact superpose eq513624 eq512313
    | exact resolve eq512313 eq513624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512313 eq513624
  have eq513811 : y = (M.op x x) := by grind
  clear eq513659
  have eq513938 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3329 x
       have i₂ := eq513811
       grind)
    | exact superpose eq513811 eq3329
    | exact resolve eq3329 eq513811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3329
  have eq514514 : y = (M.op x y) := by
    first
    | (have i₁ := eq24 x x
       have i₂ := eq513811
       grind)
    | exact superpose eq513811 eq24
    | exact resolve eq24 eq513811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq513811
  have eq519881 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq513938
       grind)
    | exact superpose eq513938 eq16
    | exact resolve eq16 eq513938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513938
  have eq519985 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq519881
       have i₂ := eq514514
       grind)
    | exact superpose eq514514 eq519881
    | exact resolve eq519881 eq514514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514514 eq519881
  have eq519986 : False := by grind
  exact eq519986

/-- `Equation3321`: `x ◇ y = x ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_pyx_x_pyx_Equation3321 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3321 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3321.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq25 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X0 X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq62 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X2 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X2 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq62 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq75 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq73 (k X0 X1) (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq73 (M.op X1 X0) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq73 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq73 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq85 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq75 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq97 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq85 (σ X0)
       grind)
    | exact superpose eq85 eq15
    | exact resolve eq15 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq85 (τ X0)
       grind)
    | exact superpose eq85 eq19
    | exact resolve eq19 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq102 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq101 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq101
    | exact resolve eq101 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq106 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq97 X0
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq97
    | exact resolve eq97 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq108 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq102
    | exact resolve eq102 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq157 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq85 (τ X0)
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq85
    | exact resolve eq85 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq160 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq157 X0
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq157
    | exact resolve eq157 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq157
  have eq197 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq14
    | (have j0 := eq14 (σ X0) X1
       grind)
    | exact resolve eq14 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq197 X0 X1
       have j1 := eq199 X0 X1
       grind)
    | (have r₁ := eq197 X0 X1
       have r₂ := eq199 X0 X1
       grind)
    | (have r₁ := eq197 X0 (σ (M.op (M.op X0 X0) (M.op X0 X0)))
       have r₂ := eq199 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq197 X0 (σ X0)
       have r₂ := eq199 X0 X1
       grind)
    | exact resolve eq197 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq199
  have eq235 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq106 (M.op (τ X0) (τ X0))
       have i₂ := eq108 X0
       grind)
    | exact superpose eq108 eq106
    | exact resolve eq106 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq245 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq235 X0
       have i₂ := eq25 (τ X0) (τ X0) (τ X0)
       grind)
    | exact superpose eq25 eq235
    | exact resolve eq235 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq248 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq245 X0
       have i₂ := eq160 X0
       grind)
    | exact superpose eq160 eq245
    | exact resolve eq245 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq245
  have eq250 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq248 X0
       have i₂ := eq25 X0 X0 X0
       grind)
    | exact superpose eq25 eq248
    | exact resolve eq248 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq248
  have eq376 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq377 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq376 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq1059 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (τ (M.op (σ X0) (σ X0))) X0)) := by
    intro X0
    first
    | (have i₁ := eq250 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq250
    | exact resolve eq250 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq1086 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (τ (σ (M.op X0 X0))) X0)) := by
    intro X0
    first
    | (have i₁ := eq1059 X0
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq1059
    | exact resolve eq1059 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq1059
  have eq1104 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq1086 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1086
    | exact resolve eq1086 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086
  have eq2899 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq201 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq201 X0 (σ X0)
       grind)
    | exact superpose eq201 eq10
    | (have j1 := eq201 X1 X0
       grind)
    | exact resolve eq10 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq6885 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq2899 (σ X0) X1
       grind)
    | exact superpose eq2899 eq15
    | (have j1 := eq2899 (σ X0) X1
       grind)
    | exact resolve eq15 eq2899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2899
  have eq6921 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6885 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6885
    | (have j0 := eq6885 X0 X1
       grind)
    | exact resolve eq6885 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6885
  have eq10023 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6921 x y
       grind)
    | exact superpose eq6921 eq16
    | (have j1 := eq6921 x y
       grind)
    | exact resolve eq16 eq6921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6921
  have eq10545 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10023
       have i₂ := eq377 y x
       grind)
    | exact superpose eq377 eq10023
    | (have j1 := eq377 y x
       grind)
    | exact resolve eq10023 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377 eq10023
  have eq10551 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by grind
  clear eq10545
  have eq10552 : x = (M.op y y) := by grind
  clear eq10551
  have eq10872 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1104 y
       have i₂ := eq10552
       grind)
    | exact superpose eq10552 eq1104
    | exact resolve eq1104 eq10552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104 eq10552
  have eq10915 : False := by grind
  exact eq10915

/-- `Equation3521`: `x ◇ y = x ◇ ((y ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pyx_x_pxy_Equation3521 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3521 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3521.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq66 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq75 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq343 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  clear eq66
  have eq1027 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq77 X1 X0
       grind)
    | exact superpose eq77 eq10
    | (have j1 := eq77 X1 X0
       grind)
    | exact resolve eq10 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq5001 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq343 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq5003 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq5001 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5001
  have eq5004 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq5003 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5003
  have eq5129 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq5004 (σ X0)
       grind)
    | exact superpose eq5004 eq15
    | exact resolve eq15 eq5004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5148 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5129 X0
       have i₂ := eq5004 X0
       grind)
    | exact superpose eq5004 eq5129
    | exact resolve eq5129 eq5004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5004 eq5129
  have eq6040 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq5148 X0
       grind)
    | exact superpose eq5148 eq9
    | exact resolve eq9 eq5148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6043 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq6118 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq6043 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq6043
    | exact resolve eq6043 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6043
  have eq6136 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq6118
  have eq6275 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq75
    | exact resolve eq75 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq6609 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6275 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq6275
    | (have j0 := eq6275 X0 X1
       grind)
    | exact resolve eq6275 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6275
  have eq7926 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq6040 X0 (σ (M.op X0 X0))
       have i₂ := eq5148 (M.op X0 X0)
       grind)
    | exact superpose eq5148 eq6040
    | exact resolve eq6040 eq5148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6040
  have eq7980 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7926 X0
       have i₂ := eq6136 (M.op X0 X0)
       grind)
    | exact superpose eq6136 eq7926
    | exact resolve eq7926 eq6136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7926
  have eq8021 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7980 X0
       have i₂ := eq9 (M.op X0 X0) X0
       grind)
    | exact superpose eq9 eq7980
    | exact resolve eq7980 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7980
  have eq39386 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq1027 X1 X0
       grind)
    | exact superpose eq1027 eq10
    | (have j1 := eq1027 X1 X0
       grind)
    | exact resolve eq10 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027
  have eq39849 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq39386 X0 X1
       have i₂ := eq5148 X0
       grind)
    | exact superpose eq5148 eq39386
    | (have j0 := eq39386 X0 X1
       grind)
    | exact resolve eq39386 eq5148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39386
  have eq40472 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq39849 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq39849
    | (have j0 := eq39849 X0 X1
       grind)
    | exact resolve eq39849 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39849
  have eq40983 : ∀ X0 X1 : G, (τ (σ (M.op X1 X1))) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq40472 X0 X1
       have i₂ := eq5148 X1
       grind)
    | exact superpose eq5148 eq40472
    | (have j0 := eq40472 X0 X1
       grind)
    | exact resolve eq40472 eq5148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5148 eq40472
  have eq41335 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq40983 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq40983
    | (have j0 := eq40983 X0 X1
       grind)
    | exact resolve eq40983 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40983
  have eq95781 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41335 x y
       grind)
    | exact superpose eq41335 eq16
    | (have j1 := eq41335 x y
       grind)
    | exact resolve eq16 eq41335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41335
  have eq96348 : x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq6609 x y
       grind)
    | (have r₁ := eq95781
       have r₂ := eq6609 y x
       grind)
    | exact resolve eq95781 eq6609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6609 eq95781
  have eq99460 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8021 y
       have i₂ := eq96348
       grind)
    | exact superpose eq96348 eq8021
    | exact resolve eq8021 eq96348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8021 eq96348
  have eq99523 : y = (M.op x x) := by
    first
    | (have r₁ := eq99460
       have r₂ := eq16
       grind)
    | exact resolve eq99460 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99460
  have eq100196 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6136 x
       have i₂ := eq99523
       grind)
    | exact superpose eq99523 eq6136
    | exact resolve eq6136 eq99523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6136 eq99523
  have eq100262 : False := by grind
  exact eq100262

/-- `Equation359`: `x ◇ x = (x ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_pyx_x_pyx_Equation359 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law359 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law359.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq37 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq37 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq48 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq46 (k X0 X1) (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq46 (M.op X1 X0) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq46 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq48 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq57 (σ X0)
       grind)
    | exact superpose eq57 eq15
    | exact resolve eq15 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq65
    | exact resolve eq65 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq65
  have eq173 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq174 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq173 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq218 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = X0 ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq42
    | (have j0 := eq42 X1 X1
       grind)
    | exact resolve eq42 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq317 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = X0 ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq218 X0 X1
       have i₂ := eq70 X1
       grind)
    | exact superpose eq70 eq218
    | (have j0 := eq218 (σ X1) X1
       grind)
    | exact resolve eq218 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq358 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq317 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq317
    | (have j0 := eq317 X0 X1
       grind)
    | exact resolve eq317 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq317
  have eq386 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq358 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq358 (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) X1
       have r₂ := eq12 (σ (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq358 X0 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq358 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq423 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0)
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq956 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq386 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq386 (σ X0) X1
       grind)
    | exact superpose eq386 eq10
    | (have j1 := eq386 X0 X1
       grind)
    | exact resolve eq10 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq2258 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq956 (σ X0) X1
       grind)
    | exact superpose eq956 eq15
    | (have j1 := eq956 (σ X0) X1
       grind)
    | exact resolve eq15 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq2294 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2258 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2258
    | (have j0 := eq2258 X0 X1
       grind)
    | exact resolve eq2258 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2258
  have eq9585 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2294 x y
       grind)
    | exact superpose eq2294 eq16
    | (have j1 := eq2294 x y
       grind)
    | exact resolve eq16 eq2294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2294
  have eq10299 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9585
       have i₂ := eq174 y x
       grind)
    | exact superpose eq174 eq9585
    | (have j1 := eq174 y x
       grind)
    | exact resolve eq9585 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq9585
  have eq10308 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by grind
  clear eq10299
  have eq10309 : x = (M.op y y) := by grind
  clear eq10308
  have eq11415 : x = (M.op x y) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq10309
       grind)
    | exact superpose eq10309 eq9
    | exact resolve eq9 eq10309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11424 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq423 y
       have i₂ := eq10309
       grind)
    | exact superpose eq10309 eq423
    | exact resolve eq423 eq10309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423 eq10309
  have eq14547 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11424
       grind)
    | exact superpose eq11424 eq16
    | exact resolve eq16 eq11424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11424
  have eq14562 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq14547
       have i₂ := eq11415
       grind)
    | exact superpose eq11415 eq14547
    | exact resolve eq14547 eq11415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11415 eq14547
  have eq14563 : False := by grind
  exact eq14563

/-- `Equation359`: `x ◇ x = (x ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pyx_pxx_pxy_Equation359 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law359 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law359.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq30 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq34 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq35 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq349 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  clear eq30
  have eq641 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq10
    | (have j1 := eq34 X1 X0
       grind)
    | exact resolve eq10 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq4229 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq349 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq4231 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4229 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4229
  have eq4232 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4231 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4231
  have eq4361 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4232 (σ X0)
       grind)
    | exact superpose eq4232 eq15
    | exact resolve eq15 eq4232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4380 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4361 X0
       have i₂ := eq4232 X0
       grind)
    | exact superpose eq4232 eq4361
    | exact resolve eq4361 eq4232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4232 eq4361
  have eq5137 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0)
       have i₂ := eq4380 X0
       grind)
    | exact superpose eq4380 eq9
    | exact resolve eq9 eq4380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5140 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq5200 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq5140 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq5140
    | exact resolve eq5140 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5140
  have eq5214 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq5200
  have eq7759 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq35 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq35
    | exact resolve eq35 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq8184 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7759 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq7759
    | (have j0 := eq7759 X0 X1
       grind)
    | exact resolve eq7759 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7759
  have eq30785 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq641 X1 X0
       grind)
    | exact superpose eq641 eq10
    | (have j1 := eq641 X1 X0
       grind)
    | exact resolve eq10 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq31183 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30785 X0 X1
       have i₂ := eq4380 X0
       grind)
    | exact superpose eq4380 eq30785
    | (have j0 := eq30785 X0 X1
       grind)
    | exact resolve eq30785 eq4380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30785
  have eq31727 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31183 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq31183
    | (have j0 := eq31183 X0 X1
       grind)
    | exact resolve eq31183 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31183
  have eq32196 : ∀ X0 X1 : G, (τ (σ (M.op X1 X1))) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31727 X0 X1
       have i₂ := eq4380 X1
       grind)
    | exact superpose eq4380 eq31727
    | (have j0 := eq31727 X0 X1
       grind)
    | exact resolve eq31727 eq4380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4380 eq31727
  have eq32522 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32196 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq32196
    | (have j0 := eq32196 X0 X1
       grind)
    | exact resolve eq32196 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32196
  have eq91876 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq32522 x y
       grind)
    | exact superpose eq32522 eq16
    | (have j1 := eq32522 x y
       grind)
    | exact resolve eq16 eq32522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32522
  have eq92282 : x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq8184 y x
       grind)
    | (have r₁ := eq91876
       have r₂ := eq8184 x y
       grind)
    | exact resolve eq91876 eq8184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8184 eq91876
  have eq93818 : x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq92282
       grind)
    | exact superpose eq92282 eq9
    | exact resolve eq9 eq92282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93836 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5137 y
       have i₂ := eq92282
       grind)
    | exact superpose eq92282 eq5137
    | exact resolve eq5137 eq92282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5137 eq92282
  have eq103453 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq93836
       grind)
    | exact superpose eq93836 eq16
    | exact resolve eq16 eq93836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93836
  have eq105765 : (σ x) ≠ (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq103453
       have i₂ := eq93818
       grind)
    | exact superpose eq93818 eq103453
    | exact resolve eq103453 eq93818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93818 eq103453
  have eq105770 : (σ x) ≠ (σ x) ∨ y = (M.op x x) := by grind
  clear eq105765
  have eq105771 : y = (M.op x x) := by grind
  clear eq105770
  have eq108738 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5214 x
       have i₂ := eq105771
       grind)
    | exact superpose eq105771 eq5214
    | exact resolve eq5214 eq105771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5214 eq105771
  have eq108792 : False := by grind
  exact eq108792

/-- `Equation359`: `x ◇ x = (x ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pyx_pxy_pyx_Equation359 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law359 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law359.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
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
  have eq30 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq36 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq73 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq36 X1 (τ X0)
       grind)
    | exact superpose eq36 eq20
    | (have j1 := eq36 X1 (τ X0)
       grind)
    | exact resolve eq20 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq75 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq36 (σ X1) (σ X0)
       grind)
    | exact superpose eq36 eq15
    | (have j1 := eq36 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    grind
  clear eq36
  have eq193 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq80 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq194 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq193 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq246 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq194 (σ X0)
       grind)
    | exact superpose eq194 eq15
    | exact resolve eq15 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq246 X0
       have i₂ := eq194 X0
       grind)
    | exact superpose eq194 eq246
    | exact resolve eq246 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq246
  have eq400 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0)
       have i₂ := eq253 X0
       grind)
    | exact superpose eq253 eq9
    | exact resolve eq9 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1853 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq73 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq73
    | exact resolve eq73 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq1980 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1853 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1853
    | (have j0 := eq1853 X0 X1
       grind)
    | exact resolve eq1853 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853
  have eq3005 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq75 X1 X0
       grind)
    | exact superpose eq75 eq10
    | (have j1 := eq75 X1 X0
       grind)
    | exact resolve eq10 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq3127 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3005 X0 X1
       have i₂ := eq253 X0
       grind)
    | exact superpose eq253 eq3005
    | (have j0 := eq3005 X0 X1
       grind)
    | exact resolve eq3005 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253 eq3005
  have eq3227 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3127 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq3127
    | (have j0 := eq3127 X0 X1
       grind)
    | exact resolve eq3127 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3127
  have eq3862 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3227 y x
       grind)
    | exact superpose eq3227 eq16
    | (have j1 := eq3227 y x
       grind)
    | exact resolve eq16 eq3227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3227
  have eq3919 : x = (M.op y y) := by
    first
    | (have j1 := eq1980 x y
       grind)
    | (have r₁ := eq3862
       have r₂ := eq1980 x y
       grind)
    | exact resolve eq3862 eq1980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1980 eq3862
  have eq4158 : x = (M.op x y) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq3919
       grind)
    | exact superpose eq3919 eq9
    | exact resolve eq9 eq3919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4169 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq400 y
       have i₂ := eq3919
       grind)
    | exact superpose eq3919 eq400
    | exact resolve eq400 eq3919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400 eq3919
  have eq4884 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4169
       grind)
    | exact superpose eq4169 eq16
    | exact resolve eq16 eq4169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4169
  have eq4886 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq4884
       have i₂ := eq4158
       grind)
    | exact superpose eq4158 eq4884
    | exact resolve eq4884 eq4158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4158 eq4884
  have eq4887 : False := by grind
  exact eq4887
