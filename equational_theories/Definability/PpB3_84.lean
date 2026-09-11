import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_Equation630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq63 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq75 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq66 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq76 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq75 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq91 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq76 (σ X0)
       grind)
    | exact superpose eq76 eq15
    | exact resolve eq15 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq91 X0
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq91
    | exact resolve eq91 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq91
  have eq118 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq176 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq167 X0 X1
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq167
    | (have j0 := eq167 X0 X1
       grind)
    | exact resolve eq167 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq641 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq176
    | (have j0 := eq176 X1 (M.op X1 X1)
       grind)
    | exact resolve eq176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq649 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq641 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq641
    | (have j0 := eq641 (σ (M.op X1 X1)) X1
       grind)
    | exact resolve eq641 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq641
  have eq653 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq649 X0 X1
       have j1 := eq118 X1 X0
       grind)
    | (have r₁ := eq649 X0 X0
       have r₂ := eq118 X0 X1
       grind)
    | (have r₁ := eq649 (σ (M.op X0 X0)) X0
       have r₂ := eq118 X0 X1
       grind)
    | (have r₁ := eq649 (σ X0) (M.op X0 X0)
       have r₂ := eq118 X0 X1
       grind)
    | exact resolve eq649 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq649
  have eq656 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq653 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq653
    | exact resolve eq653 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq667 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq653 (σ X1) X0
       grind)
    | exact superpose eq653 eq15
    | (have j1 := eq653 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq696 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq656 (τ X0) X1
       grind)
    | exact superpose eq656 eq19
    | (have j1 := eq656 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq656
  have eq781 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq696 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq696
    | exact resolve eq696 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq831 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq781 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq781
    | (have j0 := eq781 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq781 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq980 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq667 x y
       grind)
    | exact superpose eq667 eq16
    | (have j1 := eq667 x y
       grind)
    | exact resolve eq16 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq994 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq980
       have i₂ := eq831 x y
       grind)
    | exact superpose eq831 eq980
    | (have j1 := eq831 (σ x) (σ y)
       grind)
    | (have r₁ := eq980
       have r₂ := eq831 x y
       grind)
    | (have r₁ := eq980
       have r₂ := eq831 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq980
       have r₂ := eq831 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq980 eq831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831 eq980
  have eq995 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq994
  have eq998 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq995
       grind)
    | exact superpose eq995 eq16
    | exact resolve eq16 eq995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995
  have eq999 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq998
       have r₂ := eq102 x
       grind)
    | exact resolve eq998 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq1000 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq999
       grind)
    | exact superpose eq999 eq16
    | exact resolve eq16 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1001 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq999
       grind)
    | exact superpose eq999 eq10
    | exact resolve eq10 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999
  have eq1047 : x = y := by
    first
    | (have i₁ := eq1001
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1001
    | exact resolve eq1001 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq1048 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1000
       have i₂ := eq102 x
       grind)
    | exact superpose eq102 eq1000
    | exact resolve eq1000 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq1000
  have eq1049 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1048
       have i₂ := eq1047
       grind)
    | exact superpose eq1047 eq1048
    | exact resolve eq1048 eq1047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047 eq1048
  have eq1050 : False := by grind
  exact eq1050

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation630 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law630 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq459 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
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
  clear eq28
  have eq460 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq3271 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq460 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq460
    | exact resolve eq460 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq3316 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3271 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3271
    | (have j0 := eq3271 X0 X1
       grind)
    | exact resolve eq3271 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3271
  have eq3576 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (σ X1) = X0 ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq459 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq459 X0 X1
       grind)
    | exact superpose eq459 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq459 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq459 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq459 (σ X1) X1
       grind)
    | exact resolve eq13 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3579 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (k (τ (σ x)) y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq459 (σ x) y
       grind)
    | exact superpose eq459 eq16
    | (have j1 := eq459 (σ x) y
       grind)
    | (have r₁ := eq16
       have r₂ := eq459 (M.op (σ x) (σ y)) (M.op x y)
       grind)
    | exact resolve eq16 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq3591 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (σ X1) = X0 ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3576 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3576
  have eq3592 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3591 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3591
  have eq3602 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k (τ (σ x)) y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3579
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq3579
    | exact resolve eq3579 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3579
  have eq3620 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3602
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3602
    | exact resolve eq3602 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3602
  have eq3852 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3592 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3592
    | exact resolve eq3592 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3592
  have eq3943 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3852 X0 X1
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq3852
    | (have j0 := eq3852 X0 X1
       grind)
    | exact resolve eq3852 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq3852
  have eq3971 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq3943 X1 X0
       grind)
    | exact superpose eq3943 eq11
    | (have j1 := eq3943 X1 X0
       grind)
    | exact resolve eq11 eq3943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3943
  have eq4090 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3971 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq3971
    | (have j0 := eq3971 X0 X1
       grind)
    | exact resolve eq3971 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3971
  have eq4113 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4090 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4090
    | (have j0 := eq4090 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq4090 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4133 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (k X0 (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq4090 X0 (τ X1)
       grind)
    | exact superpose eq4090 eq19
    | (have j1 := eq4090 X0 (τ X1)
       grind)
    | exact resolve eq19 eq4090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq4090
  have eq4271 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4113 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq4113
    | (have j0 := eq4113 X0 X1
       grind)
    | exact resolve eq4113 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4113
  have eq4384 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4133 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4133
    | exact resolve eq4133 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4133
  have eq4436 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4384 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4384
    | (have j0 := eq4384 X0 X1
       grind)
    | exact resolve eq4384 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4384
  have eq12662 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4271 x y
       grind)
    | exact superpose eq4271 eq16
    | (have j1 := eq4271 x y
       grind)
    | exact resolve eq16 eq4271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4271
  have eq12734 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq12662
       have i₂ := eq3316 y x
       grind)
    | exact superpose eq3316 eq12662
    | (have j1 := eq3316 y x
       grind)
    | (have r₁ := eq12662
       have r₂ := eq3316 y x
       grind)
    | (have r₁ := eq12662
       have r₂ := eq3316 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq12662
       have r₂ := eq3316 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq12662 eq3316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12662
  have eq12735 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ x = y := by grind
  clear eq12734
  have eq12860 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq3620
       have i₂ := eq12735
       grind)
    | exact superpose eq12735 eq3620
    | (have r₁ := eq3620
       have r₂ := eq12735
       grind)
    | exact resolve eq3620 eq12735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12735
  have eq12864 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ x = y := by grind
  clear eq12860
  have eq12865 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ x = y := by grind
  clear eq12864
  have eq12866 : x = y ∨ (σ x) = (σ y) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq12865
       have r₂ := eq3620
       grind)
    | exact resolve eq12865 eq3620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3620 eq12865
  have eq12867 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12866
       grind)
    | exact superpose eq12866 eq16
    | exact resolve eq16 eq12866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12866
  have eq12868 : (σ x) = (σ y) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq12867
       have r₂ := eq22 x
       grind)
    | exact resolve eq12867 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12867
  have eq12870 : y = (τ (σ x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq12868
       grind)
    | exact superpose eq12868 eq10
    | exact resolve eq10 eq12868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12868
  have eq12936 : x = y ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq12870
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq12870
    | exact resolve eq12870 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12870
  have eq12938 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12936
       grind)
    | exact superpose eq12936 eq16
    | exact resolve eq16 eq12936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12936
  have eq12939 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq12938
       have r₂ := eq22 x
       grind)
    | exact resolve eq12938 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq12938
  have eq12952 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq12939
       grind)
    | exact superpose eq12939 eq11
    | exact resolve eq11 eq12939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12939
  have eq13040 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12952
       grind)
    | exact superpose eq12952 eq16
    | exact resolve eq16 eq12952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12952
  have eq13063 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq13040
       have i₂ := eq4436 y x
       grind)
    | exact superpose eq4436 eq13040
    | (have j1 := eq4436 y x
       grind)
    | (have r₁ := eq13040
       have r₂ := eq4436 y x
       grind)
    | (have r₁ := eq13040
       have r₂ := eq4436 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq13040
       have r₂ := eq4436 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq13040 eq4436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4436
  have eq13064 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq13040
       have i₂ := eq3316 y x
       grind)
    | exact superpose eq3316 eq13040
    | (have j1 := eq3316 y x
       grind)
    | (have r₁ := eq13040
       have r₂ := eq3316 y x
       grind)
    | (have r₁ := eq13040
       have r₂ := eq3316 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq13040
       have r₂ := eq3316 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq13040 eq3316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3316
  have eq13065 : (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq13064
  have eq13066 : x = y ∨ (k x y) = (M.op x x) := by grind
  clear eq13063
  have eq13222 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq13040
       have i₂ := eq13066
       grind)
    | exact superpose eq13066 eq13040
    | exact resolve eq13040 eq13066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13066
  have eq13223 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by grind
  clear eq13222
  have eq13224 : (k x y) = (M.op x x) := by grind
  clear eq13223
  have eq13233 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq13040
       have i₂ := eq13224
       grind)
    | exact superpose eq13224 eq13040
    | exact resolve eq13040 eq13224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13040 eq13224
  have eq13265 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq13233
       have i₂ := eq13065
       grind)
    | exact superpose eq13065 eq13233
    | exact resolve eq13233 eq13065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13065
  have eq13268 : x = y := by grind
  clear eq13265
  have eq13278 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq13233
       have i₂ := eq13268
       grind)
    | exact superpose eq13268 eq13233
    | exact resolve eq13233 eq13268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13233 eq13268
  have eq13279 : False := by grind
  exact eq13279

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation630 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law630 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq451 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 := by
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
  have eq3062 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq451 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq451
    | exact resolve eq451 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq3106 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3062 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3062
    | (have j0 := eq3062 X0 X1
       grind)
    | exact resolve eq3062 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3062
  have eq3110 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (M.op (τ X0) (τ X1))) ∨ (M.op (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3106 (τ X1) (τ X0)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq3106
    | (have j0 := eq3106 (τ X0) (τ X1)
       grind)
    | exact resolve eq3106 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3106
  have eq3203 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3110 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq3110
    | (have j0 := eq3110 X0 X1
       grind)
    | exact resolve eq3110 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3110
  have eq18855 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) ≠ (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) (τ X0)
       have i₂ := eq3203 X0 X1
       grind)
    | (have i₁ := eq13 (τ X0) (τ X1)
       have i₂ := eq3203 X0 X1
       grind)
    | exact superpose eq3203 eq13
    | (have j0 := eq13 (τ X0) (τ X1)
       have j1 := eq3203 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq3203 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) (τ X0)
       have r₂ := eq3203 X0 X1
       grind)
    | exact resolve eq13 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3203
  have eq18859 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) ≠ (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq18855 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18855
  have eq18860 : ∀ X0 X1 : G, (τ X0) = (τ X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq18859 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18859
  have eq18876 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18860 X0 X1
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq18860
    | (have j0 := eq18860 X0 X1
       grind)
    | exact resolve eq18860 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq18860
  have eq25424 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (M.op (τ X1) X0) ∨ (τ X1) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18876 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18876
    | exact resolve eq18876 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18876
  have eq25508 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25424 X0 X1
       have i₂ := eq28 X1 X0
       grind)
    | exact superpose eq28 eq25424
    | (have j0 := eq25424 X0 X1
       grind)
    | exact resolve eq25424 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25424
  have eq25578 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) X1)
       have i₂ := eq25508 X1 X0
       grind)
    | exact superpose eq25508 eq10
    | (have j1 := eq25508 X1 X0
       grind)
    | exact resolve eq10 eq25508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25508
  have eq25691 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25578 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq25578
    | (have j0 := eq25578 X0 X1
       grind)
    | exact resolve eq25578 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq25578
  have eq25692 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq25691 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25691
  have eq25759 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25692 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25692
    | exact resolve eq25692 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25806 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq25692 X0 X1
       grind)
    | exact superpose eq25692 eq18
    | (have j1 := eq25692 X0 X1
       grind)
    | exact resolve eq18 eq25692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq25692
  have eq26144 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq25759 (σ X0) (σ X1)
       grind)
    | exact superpose eq25759 eq15
    | (have j1 := eq25759 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq25759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25759
  have eq26282 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25806 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25806
    | exact resolve eq25806 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25806
  have eq26471 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26282 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq26282
    | (have j0 := eq26282 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq26282 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26282
  have eq28056 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26144 x y
       grind)
    | exact superpose eq26144 eq16
    | (have j1 := eq26144 x y
       grind)
    | exact resolve eq16 eq26144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26144
  have eq28111 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq28056
       have i₂ := eq26471 x y
       grind)
    | exact superpose eq26471 eq28056
    | (have j1 := eq26471 (σ x) (σ y)
       grind)
    | (have r₁ := eq28056
       have r₂ := eq26471 x y
       grind)
    | (have r₁ := eq28056
       have r₂ := eq26471 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq28056
       have r₂ := eq26471 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq28056 eq26471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26471 eq28056
  have eq28116 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq28111
  have eq28120 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28116
       grind)
    | exact superpose eq28116 eq16
    | exact resolve eq16 eq28116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28116
  have eq28121 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq28120
       have r₂ := eq22 x
       grind)
    | exact resolve eq28120 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28120
  have eq28122 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28121
       grind)
    | exact superpose eq28121 eq16
    | exact resolve eq16 eq28121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28123 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq28121
       grind)
    | exact superpose eq28121 eq10
    | exact resolve eq10 eq28121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28121
  have eq28294 : x = y := by
    first
    | (have i₁ := eq28123
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq28123
    | exact resolve eq28123 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28123
  have eq28295 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq28122
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq28122
    | exact resolve eq28122 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq28122
  have eq28296 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq28295
       have i₂ := eq28294
       grind)
    | exact superpose eq28294 eq28295
    | exact resolve eq28295 eq28294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28294 eq28295
  have eq28297 : False := by grind
  exact eq28297

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation630 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law630 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  clear eq28
  have eq63 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq156 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (M.op X1 (τ X0)) ∨ (τ X0) = X1 ∨ (k X1 (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (τ X0)
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq13
    | (have j0 := eq13 (τ X0) X1
       grind)
    | exact resolve eq13 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq328 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq331 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq343 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq331 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq331
    | (have j0 := eq331 X0 X1
       grind)
    | exact resolve eq331 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq344 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ (M.op X1 X1)) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq328 X0 X1
       have i₂ := eq63 X1
       grind)
    | exact superpose eq63 eq328
    | (have j0 := eq328 X0 X1
       grind)
    | exact resolve eq328 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq659 : ∀ X0 X1 : G, (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (M.op (σ X1) (σ X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq343 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq343
    | (have j0 := eq343 (σ X0) (σ X1)
       grind)
    | exact resolve eq343 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq707 : ∀ X0 X1 : G, (σ (σ (M.op X1 X1))) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq659 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq659
    | (have j0 := eq659 X0 X1
       grind)
    | exact resolve eq659 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq3398 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op X0 (τ X1)) ∨ (τ (M.op X1 X1)) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 (τ X1))
       have i₂ := eq344 X0 X1
       grind)
    | exact superpose eq344 eq10
    | (have j1 := eq344 X0 X1
       grind)
    | exact resolve eq10 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq3463 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (τ (M.op X1 X1)) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3398 X0 X1
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq3398
    | (have j0 := eq3398 X0 X1
       grind)
    | exact resolve eq3398 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq3398
  have eq9886 : ∀ X0 X1 : G, (σ (σ (M.op X1 X1))) ≠ (σ (σ (k X0 X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq707 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq209193 : ∀ X0 X1 : G, (σ (σ (M.op (τ X1) (τ X1)))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ (k X0 X1)))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9886 (τ X1) (τ X0)
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq9886
    | (have j0 := eq9886 (τ X0) (τ X1)
       grind)
    | exact resolve eq9886 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9886
  have eq209661 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (M.op (τ X1) (τ X1)))) ∨ (σ (σ (τ (k X0 X1)))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq209193 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq209193
    | (have j0 := eq209193 X0 X1
       grind)
    | exact resolve eq209193 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209193
  have eq209904 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ (M.op X1 X1)))) ∨ (σ (σ (τ (k X0 X1)))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq209661 X0 X1
       have i₂ := eq63 X1
       grind)
    | exact superpose eq63 eq209661
    | (have j0 := eq209661 X0 X1
       grind)
    | exact resolve eq209661 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209661
  have eq210128 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (σ (τ (k X0 X1)))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq209904 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq209904
    | (have j0 := eq209904 X0 X1
       grind)
    | exact resolve eq209904 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209904
  have eq210345 : ∀ X0 X1 : G, (σ (σ (τ (k X0 X1)))) = (M.op (σ (σ (τ X0))) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq210128 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq210128
    | (have j0 := eq210128 X0 X1
       grind)
    | exact resolve eq210128 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210128
  have eq210525 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (σ (τ (k X0 X1)))) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq210345 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq210345
    | (have j0 := eq210345 X0 X1
       grind)
    | exact resolve eq210345 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210345
  have eq210687 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq210525 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq210525
    | (have j0 := eq210525 X0 X1
       grind)
    | exact resolve eq210525 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210525
  have eq210804 : ∀ X0 X1 : G, (σ X1) = (σ (σ (τ X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq210687 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq210687
    | (have j0 := eq210687 X0 X1
       grind)
    | exact resolve eq210687 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210687
  have eq210919 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq210804 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq210804
    | (have j0 := eq210804 X0 X1
       grind)
    | exact resolve eq210804 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210804
  have eq211132 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq210919 (τ X1) (τ X0)
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq210919
    | (have j0 := eq210919 (τ X0) (τ X1)
       grind)
    | exact resolve eq210919 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq210919
  have eq211614 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (τ (M.op X1 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq211132 X0 X1
       have i₂ := eq63 X1
       grind)
    | exact superpose eq63 eq211132
    | (have j0 := eq211132 X0 X1
       grind)
    | exact resolve eq211132 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211132
  have eq211857 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq211614 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq211614
    | (have j0 := eq211614 X0 X1
       grind)
    | exact resolve eq211614 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211614
  have eq212078 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq211857 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq211857
    | (have j0 := eq211857 X0 X1
       grind)
    | exact resolve eq211857 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211857
  have eq212295 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq212078 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq212078
    | (have j0 := eq212078 X0 X1
       grind)
    | exact resolve eq212078 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212078
  have eq212473 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq212295 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq212295
    | (have j0 := eq212295 X0 X1
       grind)
    | exact resolve eq212295 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212295
  have eq212633 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq212473 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq212473
    | (have j0 := eq212473 X0 X1
       grind)
    | exact resolve eq212473 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212473
  have eq212749 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq212633 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq212633
    | (have j0 := eq212633 X0 X1
       grind)
    | exact resolve eq212633 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212633
  have eq212863 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq212749 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq212749
    | (have j0 := eq212749 X0 X1
       grind)
    | exact resolve eq212749 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212749
  have eq213201 : ∀ X0 X1 : G, (k X1 (τ X0)) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq212863 X1 (τ X0)
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq212863
    | (have j0 := eq212863 X1 (τ X0)
       grind)
    | exact resolve eq212863 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq212863
  have eq213202 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq213201 X0 X1
       have j1 := eq3463 X1 X0
       have j2 := eq156 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156 eq3463 eq213201
  have eq213258 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq213202 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq213202
    | exact resolve eq213202 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213202
  have eq214406 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq213258 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq213258
    | (have j0 := eq213258 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq213258 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217709 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq214406 X0 X1
       have i₂ := eq213258 X1 X0
       grind)
    | exact superpose eq213258 eq214406
    | (have j0 := eq214406 X0 X1
       have j1 := eq213258 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq214406 eq213258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213258 eq214406
  have eq220856 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq217709 x y
       grind)
    | exact superpose eq217709 eq16
    | (have j1 := eq217709 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq217709 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq217709 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq217709 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq217709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217709
  have eq220875 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq220856
  have eq220906 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq220875
       grind)
    | exact superpose eq220875 eq10
    | exact resolve eq10 eq220875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220875
  have eq221085 : x = y ∨ x = y := by
    first
    | (have i₁ := eq220906
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq220906
    | exact resolve eq220906 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220906
  have eq221086 : x = y := by grind
  clear eq221085
  have eq221089 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq221086
       grind)
    | exact superpose eq221086 eq16
    | exact resolve eq16 eq221086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221086
  have eq221090 : False := by grind
  exact eq221090

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation630 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law630 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  clear eq19
  have eq150 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq152 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
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
  have eq715 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) X0
       have i₂ := eq152 X1 X0
       grind)
    | exact superpose eq152 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq152 X1 X0
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq152 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X0)
       have r₂ := eq152 X0 (M.op X0 (τ X0))
       grind)
    | exact resolve eq13 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq716 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq715 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq717 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (k (τ X1) X0) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq716 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq776 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq150 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq2264 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq717 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq717
    | exact resolve eq717 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq2318 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2264 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2264
    | (have j0 := eq2264 X0 X1
       grind)
    | exact resolve eq2264 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2264
  have eq2363 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq2318 X0 X1
       grind)
    | exact superpose eq2318 eq10
    | (have j1 := eq2318 X0 X1
       grind)
    | exact resolve eq10 eq2318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2406 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2363 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq2363
    | (have j0 := eq2363 X0 X1
       grind)
    | exact resolve eq2363 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2363
  have eq2444 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq2406 (σ X0) X1
       grind)
    | exact superpose eq2406 eq37
    | (have j1 := eq2406 (σ X0) X1
       grind)
    | exact resolve eq37 eq2406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2406
  have eq4288 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X1) X0
       have i₂ := eq2444 X1 (σ X0)
       grind)
    | exact superpose eq2444 eq28
    | (have j1 := eq2444 X1 (σ X0)
       grind)
    | exact resolve eq28 eq2444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2444
  have eq4349 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4288 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4288
    | (have j0 := eq4288 X0 X1
       grind)
    | exact resolve eq4288 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4288
  have eq4383 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4349 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4349
    | (have j0 := eq4349 X0 X1
       grind)
    | exact resolve eq4349 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4349
  have eq4393 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4383 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4383
    | (have j0 := eq4383 X0 X1
       grind)
    | exact resolve eq4383 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4383
  have eq4596 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq4393 X1 X0
       grind)
    | exact superpose eq4393 eq11
    | (have j1 := eq4393 X1 X0
       grind)
    | exact resolve eq11 eq4393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4393
  have eq5473 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4596 x y
       grind)
    | exact superpose eq4596 eq16
    | (have j1 := eq4596 x y
       grind)
    | exact resolve eq16 eq4596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4596
  have eq5499 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5473
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq5473
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq5473
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5473
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5473 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5500 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq5473
       have i₂ := eq2318 x y
       grind)
    | exact superpose eq2318 eq5473
    | (have j1 := eq2318 x y
       grind)
    | (have r₁ := eq5473
       have r₂ := eq2318 x y
       grind)
    | (have r₁ := eq5473
       have r₂ := eq2318 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5473
       have r₂ := eq2318 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5473 eq2318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2318 eq5473
  have eq5503 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5500
  have eq5504 : x = y ∨ (σ x) = (σ y) ∨ y = (k x y) := by grind
  clear eq5503
  have eq5505 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5499
  have eq5506 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5505
  have eq5510 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5504
       grind)
    | exact superpose eq5504 eq16
    | exact resolve eq16 eq5504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5504
  have eq5511 : y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5510
       have r₂ := eq22 x
       grind)
    | exact resolve eq5510 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5510
  have eq5516 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq776 x y
       have i₂ := eq5511
       grind)
    | exact superpose eq5511 eq776
    | (have j0 := eq776 x y
       grind)
    | exact resolve eq776 eq5511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776 eq5511
  have eq5522 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5516
  have eq5523 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5522
  have eq5535 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5523
       grind)
    | exact superpose eq5523 eq16
    | exact resolve eq16 eq5523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5523
  have eq5552 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5535
       have i₂ := eq5506
       grind)
    | exact superpose eq5506 eq5535
    | exact resolve eq5535 eq5506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5506 eq5535
  have eq5553 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5552
  have eq5554 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq5553
  have eq5555 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5554
       grind)
    | exact superpose eq5554 eq16
    | exact resolve eq16 eq5554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5554
  have eq5556 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq5555
       have r₂ := eq22 x
       grind)
    | exact resolve eq5555 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5555
  have eq5557 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5556
       grind)
    | exact superpose eq5556 eq16
    | exact resolve eq16 eq5556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5558 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5556
       grind)
    | exact superpose eq5556 eq10
    | exact resolve eq10 eq5556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5556
  have eq5612 : x = y := by
    first
    | (have i₁ := eq5558
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5558
    | exact resolve eq5558 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5558
  have eq5613 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5557
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5557
    | exact resolve eq5557 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5557
  have eq5614 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5613
       have i₂ := eq5612
       grind)
    | exact superpose eq5612 eq5613
    | exact resolve eq5613 eq5612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5612 eq5613
  have eq5615 : False := by grind
  exact eq5615

/-- `Equation639`: `x = x ◇ (y ◇ ((y ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pxy_y_pxy_Equation639 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law639 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law639.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq88 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq24
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq24 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq281 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq81 x y
       grind)
    | exact superpose eq81 eq16
    | (have j1 := eq81 x y
       grind)
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq854 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq288 (τ X0) (τ X1)
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq288
    | (have j0 := eq288 (τ X0) (τ X1)
       grind)
    | exact resolve eq288 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq872 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq854 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq854
    | (have j0 := eq854 X0 X1
       grind)
    | exact resolve eq854 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq880 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq872 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq872
    | (have j0 := eq872 X0 X1
       grind)
    | exact resolve eq872 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq887 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq880 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq880
    | (have j0 := eq880 X0 X1
       grind)
    | exact resolve eq880 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq893 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq887 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq887
    | (have j0 := eq887 X0 X1
       grind)
    | exact resolve eq887 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq898 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq893 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq893
    | (have j0 := eq893 X0 X1
       grind)
    | exact resolve eq893 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq901 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq898 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq898
    | (have j0 := eq898 X0 X1
       grind)
    | exact resolve eq898 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq4454 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq88 X1 X0
       grind)
    | exact superpose eq88 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq88 X1 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq88 (σ X1) X1
       grind)
    | exact resolve eq13 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq4485 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq4454 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4454
  have eq4486 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (σ X0) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4485 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4485
  have eq78447 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (σ X1) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 (σ X1))
       have i₂ := eq4486 X1 X0
       grind)
    | exact superpose eq4486 eq11
    | (have j1 := eq4486 X1 X0
       grind)
    | exact resolve eq11 eq4486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4486
  have eq78607 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (σ X1) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq78447 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq78447
    | (have j0 := eq78447 X0 X1
       grind)
    | exact resolve eq78447 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78447
  have eq78661 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq78607 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq78607 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq78607 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78607
  have eq78932 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq78661 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq78661
    | exact resolve eq78661 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78966 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq78661 (σ X0) X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq78661
    | exact resolve eq78661 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78661
  have eq79418 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq78932 X1 (τ X0)
       grind)
    | exact superpose eq78932 eq17
    | (have j1 := eq78932 X1 (τ X0)
       grind)
    | exact resolve eq17 eq78932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq78932
  have eq82528 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79418 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq79418
    | exact resolve eq79418 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79418
  have eq82878 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82528 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq82528
    | (have j0 := eq82528 X0 X1
       grind)
    | exact resolve eq82528 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82528
  have eq83048 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq82878 (τ X1) (τ X0)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq82878
    | exact resolve eq82878 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq82878
  have eq83390 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq83048 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq83048
    | (have j0 := eq83048 X0 X1
       grind)
    | exact resolve eq83048 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83048
  have eq84146 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq78966 x y
       grind)
    | exact superpose eq78966 eq16
    | (have j1 := eq78966 x y
       grind)
    | exact resolve eq16 eq78966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78966
  have eq88270 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq83390 X1 X0
       grind)
    | exact superpose eq83390 eq11
    | (have j1 := eq83390 X1 X0
       grind)
    | exact resolve eq11 eq83390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83390
  have eq88492 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq88270 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq88270
    | (have j0 := eq88270 X0 X1
       grind)
    | exact resolve eq88270 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88270
  have eq88702 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq88492 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq88492
    | (have j0 := eq88492 X1 (σ X0)
       grind)
    | exact resolve eq88492 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88492
  have eq91447 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq88702 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq88702
    | (have j0 := eq88702 X1 (σ X0)
       grind)
    | exact resolve eq88702 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88702
  have eq91800 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq91447 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq91447
    | (have j0 := eq91447 X0 X1
       grind)
    | exact resolve eq91447 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91447
  have eq91857 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq91800 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq91800
    | (have j0 := eq91800 X0 X1
       grind)
    | exact resolve eq91800 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91800
  have eq93432 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq84146
       have i₂ := eq91857 y x
       grind)
    | exact superpose eq91857 eq84146
    | (have j1 := eq91857 y x
       grind)
    | (have r₁ := eq84146
       have r₂ := eq91857 y x
       grind)
    | exact resolve eq84146 eq91857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84146
  have eq93433 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq281
       have i₂ := eq91857 y x
       grind)
    | exact superpose eq91857 eq281
    | (have j1 := eq91857 y x
       grind)
    | (have r₁ := eq281
       have r₂ := eq91857 y x
       grind)
    | exact resolve eq281 eq91857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq93600 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq91857 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91857
  have eq93601 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq93433
  have eq93602 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq93432
  have eq93670 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq288 x y
       grind)
    | (have r₁ := eq93601
       have r₂ := eq288 x y
       grind)
    | exact resolve eq93601 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288 eq93601
  have eq93671 : (σ y) = (σ (k x y)) := by
    first
    | (have j1 := eq93600 x y
       grind)
    | (have r₁ := eq93602
       have r₂ := eq93600 x y
       grind)
    | exact resolve eq93602 eq93600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93600 eq93602
  have eq94401 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq93671
       grind)
    | exact superpose eq93671 eq10
    | exact resolve eq10 eq93671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94638 : y = (k x y) := by
    first
    | (have i₁ := eq94401
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq94401
    | exact resolve eq94401 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94401
  have eq94704 : y ≠ y ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq901 x y
       have i₂ := eq94638
       grind)
    | exact superpose eq94638 eq901
    | (have j0 := eq901 x y
       grind)
    | (have r₁ := eq901 x y
       have r₂ := eq94638
       grind)
    | exact resolve eq901 eq94638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq94724 : y = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq94704
  have eq95167 : y ≠ y ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq94724
       grind)
    | exact superpose eq94724 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq94724
       grind)
    | exact resolve eq12 eq94724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94724
  have eq95187 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by grind
  clear eq95167
  have eq95191 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq95187
       have i₂ := eq94638
       grind)
    | exact superpose eq94638 eq95187
    | exact resolve eq95187 eq94638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94638 eq95187
  have eq95192 : y = (M.op x y) := by grind
  clear eq95191
  have eq103103 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq93670
       grind)
    | exact superpose eq93670 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq93670
       grind)
    | exact resolve eq12 eq93670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93670
  have eq103124 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq103103
  have eq103143 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq103124
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq103124
    | exact resolve eq103124 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103124
  have eq103170 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq103143
       have i₂ := eq93671
       grind)
    | exact superpose eq93671 eq103143
    | exact resolve eq103143 eq93671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93671 eq103143
  have eq103171 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq103170
  have eq103563 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq103171
       grind)
    | exact superpose eq103171 eq16
    | exact resolve eq16 eq103171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103171
  have eq103652 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq103563
       have i₂ := eq95192
       grind)
    | exact superpose eq95192 eq103563
    | exact resolve eq103563 eq95192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95192 eq103563
  have eq103653 : False := by grind
  exact eq103653

/-- `Equation639`: `x = x ◇ (y ◇ ((y ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxy_pxx_pxy_Equation639 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law639 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law639.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq62 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq63 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq62 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq62
    | (have j0 := eq62 X0
       grind)
    | exact resolve eq62 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq85 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq204 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq83 x y
       grind)
    | exact superpose eq83 eq16
    | (have j1 := eq83 x y
       grind)
    | exact resolve eq16 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq328 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq63 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq63
    | exact resolve eq63 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq351 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq328 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq328
    | (have j0 := eq328 X0
       grind)
    | exact resolve eq328 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq352 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (σ (k X0 X0))) = (σ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq351 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq351
    | (have j0 := eq351 (σ X0)
       grind)
    | exact resolve eq351 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq444 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq85 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq85
    | exact resolve eq85 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq478 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq444 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq444
    | (have j0 := eq444 X0 X1
       grind)
    | exact resolve eq444 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq784 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq204
       have i₂ := eq478 x y
       grind)
    | exact superpose eq478 eq204
    | (have j1 := eq478 (σ x) (σ y)
       grind)
    | (have r₁ := eq204
       have r₂ := eq478 x y
       grind)
    | (have r₁ := eq204
       have r₂ := eq478 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq204
       have r₂ := eq478 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq204 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq478
  have eq785 : x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq784
  have eq6151 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (σ (σ (k X0 X0))) = (σ (M.op (σ X0) (σ X0))) := by
    intro X0
    grind
  clear eq352
  have eq6160 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ (σ (k X0 X0))) = (σ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq6151 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq6151
    | (have j0 := eq6151 X0
       grind)
    | exact resolve eq6151 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6151
  have eq12375 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq785
       grind)
    | exact superpose eq785 eq16
    | exact resolve eq16 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq21665 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (σ (M.op X0 X0)) = (σ (σ (k (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq6160 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6160
    | exact resolve eq6160 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6160
  have eq21834 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (σ (M.op X0 X0)) = (σ (σ (k (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq21665 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq21665
    | (have j0 := eq21665 X0
       grind)
    | exact resolve eq21665 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21665
  have eq21861 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (M.op X0 X0)) = (σ (σ (k (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq21834 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21834
    | (have j0 := eq21834 X0
       grind)
    | exact resolve eq21834 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21834
  have eq21866 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k (σ (τ X0)) X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq21861 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq21861
    | (have j0 := eq21861 X0
       grind)
    | exact resolve eq21861 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq21861
  have eq21868 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq21866 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21866
    | (have j0 := eq21866 X0
       grind)
    | exact resolve eq21866 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21866
  have eq22338 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq21868 X0
       grind)
    | exact superpose eq21868 eq10
    | (have j1 := eq21868 X0
       grind)
    | exact resolve eq10 eq21868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21868
  have eq22438 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq22338 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq22338
    | (have j0 := eq22338 X0
       grind)
    | exact resolve eq22338 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22338
  have eq22439 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq22438 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22438
  have eq22540 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq22439 (σ X0)
       grind)
    | exact superpose eq22439 eq15
    | exact resolve eq15 eq22439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22626 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq22540 X0
       have i₂ := eq22439 X0
       grind)
    | exact superpose eq22439 eq22540
    | exact resolve eq22540 eq22439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22439 eq22540
  have eq24268 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq24324 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq24268 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq24268
    | exact resolve eq24268 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24268
  have eq24372 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq24324
  have eq1754864 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12375
       have i₂ := eq22626 x
       grind)
    | exact superpose eq22626 eq12375
    | (have r₁ := eq12375
       have r₂ := eq22626 x
       grind)
    | exact resolve eq12375 eq22626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12375
  have eq1754936 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq1754864
  have eq1755008 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1754936
       have i₂ := eq22626 y
       grind)
    | exact superpose eq22626 eq1754936
    | exact resolve eq1754936 eq22626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1754936
  have eq1755407 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq24372 y
       have i₂ := eq1755008
       grind)
    | exact superpose eq1755008 eq24372
    | exact resolve eq24372 eq1755008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1755008
  have eq1755515 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1755407
       have r₂ := eq16
       grind)
    | exact resolve eq1755407 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1755407
  have eq1759674 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1755515
       grind)
    | exact superpose eq1755515 eq10
    | exact resolve eq10 eq1755515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1755515
  have eq1760452 : x = y ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1759674
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1759674
    | exact resolve eq1759674 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1759674
  have eq1760803 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1760452
       grind)
    | exact superpose eq1760452 eq16
    | exact resolve eq16 eq1760452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1760452
  have eq1760804 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1760803
       have r₂ := eq22626 x
       grind)
    | exact resolve eq1760803 eq22626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22626 eq1760803
  have eq1765455 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1760804
       grind)
    | exact superpose eq1760804 eq10
    | exact resolve eq10 eq1760804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1760804
  have eq1766230 : x = (M.op y y) := by
    first
    | (have i₁ := eq1765455
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1765455
    | exact resolve eq1765455 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1765455
  have eq1766951 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24372 y
       have i₂ := eq1766230
       grind)
    | exact superpose eq1766230 eq24372
    | exact resolve eq24372 eq1766230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24372 eq1766230
  have eq1766985 : False := by grind
  exact eq1766985

/-- `Equation639`: `x = x ◇ (y ◇ ((y ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pxx_pxy_Equation639 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law639 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law639.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq54 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq54 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq54 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq55 (σ X0)
       grind)
    | exact superpose eq55 eq15
    | exact resolve eq15 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq55 (τ X0)
       grind)
    | exact superpose eq55 eq18
    | exact resolve eq18 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60
    | exact resolve eq60 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq57
    | exact resolve eq57 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq63
    | exact resolve eq63 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq63
  have eq79 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq91 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 X1
       have i₂ := eq66 X1
       grind)
    | exact superpose eq66 eq91
    | (have j0 := eq91 X0 X1
       grind)
    | exact resolve eq91 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq178 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq93
    | (have j0 := eq93 X0 X1
       grind)
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq205 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq178
    | (have j0 := eq178 X0 X1
       grind)
    | exact resolve eq178 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq178
  have eq209 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq205 X0 X1
       have j1 := eq80 X1 X0
       grind)
    | (have r₁ := eq205 X0 X0
       have r₂ := eq80 X0 X1
       grind)
    | exact resolve eq205 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq213 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq209 X0 X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq209
    | (have j0 := eq209 X0 X1
       grind)
    | exact resolve eq209 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq209
  have eq371 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq213 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq213
    | exact resolve eq213 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq382 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq213 (σ X0) X1
       grind)
    | exact superpose eq213 eq15
    | (have j1 := eq213 (σ X0) X1
       grind)
    | exact resolve eq15 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq393 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq382 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq382
    | (have j0 := eq382 X0 X1
       grind)
    | exact resolve eq382 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq408 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq371 (τ X1) X0
       grind)
    | exact superpose eq371 eq18
    | (have j1 := eq371 (τ X1) X0
       grind)
    | exact resolve eq18 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq371
  have eq943 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq408 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq408
    | exact resolve eq408 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq989 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq943 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq943
    | (have j0 := eq943 X0 X1
       grind)
    | exact resolve eq943 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943
  have eq3499 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq393 x y
       grind)
    | exact superpose eq393 eq16
    | (have j1 := eq393 x y
       grind)
    | exact resolve eq16 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3523 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq393 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq3689 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3499
       have i₂ := eq989 y x
       grind)
    | exact superpose eq989 eq3499
    | (have j1 := eq989 y x
       grind)
    | (have r₁ := eq3499
       have r₂ := eq989 y x
       grind)
    | exact resolve eq3499 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3499
  have eq3690 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3689
  have eq3696 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ y = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq3690
       grind)
    | exact superpose eq3690 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq3690
       grind)
    | exact resolve eq13 eq3690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3690
  have eq3698 : (k x y) = (M.op x x) ∨ y = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3696
  have eq17999 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3523 x y
       have i₂ := eq3698
       grind)
    | exact superpose eq3698 eq3523
    | (have j0 := eq3523 x y
       grind)
    | exact resolve eq3523 eq3698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3523 eq3698
  have eq18010 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op y y) := by grind
  clear eq17999
  have eq18011 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op y y) := by grind
  clear eq18010
  have eq18397 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18011
       grind)
    | exact superpose eq18011 eq16
    | exact resolve eq16 eq18011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18398 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq79 x (σ y)
       have i₂ := eq18011
       grind)
    | exact superpose eq18011 eq79
    | (have j0 := eq79 x (σ y)
       grind)
    | (have r₁ := eq79 x (σ y)
       have r₂ := eq18011
       grind)
    | exact resolve eq79 eq18011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq18011
  have eq18417 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq18398
  have eq18425 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq18417
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq18417
    | exact resolve eq18417 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18417
  have eq18430 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq18425
       have i₂ := eq66 y
       grind)
    | exact superpose eq66 eq18425
    | exact resolve eq18425 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq18425
  have eq18833 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq989 y x
       have i₂ := eq18430
       grind)
    | exact superpose eq18430 eq989
    | (have j0 := eq989 y x
       grind)
    | exact resolve eq989 eq18430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18430
  have eq18933 : (M.op x y) = (M.op x x) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq18833
       have r₂ := eq18397
       grind)
    | exact resolve eq18833 eq18397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18833
  have eq19256 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq18397
       have i₂ := eq18933
       grind)
    | exact superpose eq18933 eq18397
    | exact resolve eq18397 eq18933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18933
  have eq19269 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq19256
  have eq19270 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq19269
  have eq19367 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq80 y X0
       have i₂ := eq19270
       grind)
    | exact superpose eq19270 eq80
    | (have j0 := eq80 y X0
       grind)
    | (have r₁ := eq80 y x
       have r₂ := eq19270
       grind)
    | exact resolve eq80 eq19270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19270
  have eq19394 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq19367 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19367
  have eq19403 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq19394 X0
       have j1 := eq80 y X0
       grind)
    | (have r₁ := eq19394 X0
       have r₂ := eq80 y x
       grind)
    | exact resolve eq19394 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq19394
  have eq19437 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq19403 (σ X0)
       grind)
    | exact superpose eq19403 eq15
    | exact resolve eq15 eq19403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19403
  have eq19954 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19437 x
       grind)
    | exact superpose eq19437 eq16
    | exact resolve eq16 eq19437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19437
  have eq20289 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19954
       have i₂ := eq989 y x
       grind)
    | exact superpose eq989 eq19954
    | (have j1 := eq989 y x
       grind)
    | (have r₁ := eq19954
       have r₂ := eq989 y x
       grind)
    | exact resolve eq19954 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq20290 : (M.op x y) = (M.op x x) := by grind
  clear eq20289
  have eq20293 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq18397
       have i₂ := eq20290
       grind)
    | exact superpose eq20290 eq18397
    | exact resolve eq18397 eq20290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18397 eq20290
  have eq20305 : y = (M.op y y) := by grind
  clear eq20293
  have eq20395 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq20305
       grind)
    | exact superpose eq20305 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq20305
       grind)
    | exact resolve eq12 eq20305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20305
  have eq20430 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq20395 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20395
  have eq20542 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq19954
       have i₂ := eq20430 x
       grind)
    | exact superpose eq20430 eq19954
    | exact resolve eq19954 eq20430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19954 eq20430
  have eq20550 : False := by grind
  exact eq20550
