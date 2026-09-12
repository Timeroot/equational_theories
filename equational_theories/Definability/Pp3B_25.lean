import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pxy_pxx_pxy_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq9 X0 (M.op X1 (M.op X2 X1)) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq42 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq42 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq56 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq82 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq43 (τ X0)
       grind)
    | exact superpose eq43 eq18
    | exact resolve eq18 eq43
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
  have eq91 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq83
    | exact resolve eq83 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq83
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
  clear eq91
  have eq109 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 (M.op X1 X2)) X0) = (M.op (M.op X4 (M.op X1 X2)) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq23 X2 X4 X1 x
       have i₂ := eq23 X2 X0 X1 x
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 (M.op X0 X1) x X1 X2
       have i₂ := eq9 X0 x X1
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) (M.op X4 (M.op X3 X4)))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X3 (M.op X1 X2) X2 X4
       have i₂ := eq23 X1 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq23 eq24
    | exact resolve eq24 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X0 X2)) (M.op (M.op X4 (M.op X5 X4)) (M.op X3 (M.op X0 (M.op X1 (M.op X2 X1)))))) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq24 (M.op X3 (M.op X0 X2)) X4 X5 X3
       have i₂ := eq23 X2 X3 X0 X1
       grind)
    | exact superpose eq23 eq24
    | exact resolve eq24 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq167 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by
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
  clear eq67
  have eq187 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq9
    | exact resolve eq9 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op X1 (M.op (σ (M.op X0 X0)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq187 X0 x
       have i₂ := eq23 (σ (M.op X0 X0)) x (σ X0) X1
       grind)
    | exact superpose eq23 eq187
    | exact resolve eq187 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq518 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq167
       have i₂ := eq95 x
       grind)
    | exact superpose eq95 eq167
    | exact resolve eq167 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq545 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq518
       have i₂ := eq56 x y
       grind)
    | exact superpose eq56 eq518
    | (have j1 := eq56 x y
       grind)
    | exact resolve eq518 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq518
  have eq546 : (M.op x x) = (M.op y x) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by grind
  clear eq545
  have eq561 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ (M.op X0 X0))) (M.op X1 (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq116 X1 (M.op (σ X0) (σ (M.op X0 X0))) X1
       have i₂ := eq187 X0 X1
       grind)
    | exact superpose eq187 eq116
    | exact resolve eq116 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq993 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X0) X3) = (M.op (M.op X1 X0) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq109 X0 (M.op (σ X0) (σ (M.op X0 X0))) (M.op X1 (σ X0)) x
       have i₂ := eq561 X0 X1
       grind)
    | exact superpose eq561 eq109
    | exact resolve eq109 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq561
  have eq1477 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq116 X2 X1 X2
       have i₂ := eq993 X1 X0 X2
       grind)
    | (have i₁ := eq116 X2 X1 X2
       have i₂ := eq993 X1 X2 X0
       grind)
    | exact superpose eq993 eq116
    | exact resolve eq116 eq993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993
  have eq2379 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (M.op X0 X1) X0) X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1477 (M.op (M.op X0 X1) X0) X2 X1
       have i₂ := eq1477 X0 X1 (M.op (M.op (M.op X0 X1) X0) X2)
       grind)
    | exact superpose eq1477 eq1477
    | exact resolve eq1477 eq1477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477
  have eq13592 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op (M.op X2 (M.op (M.op X3 X0) X3)) X2) X1)) (M.op (M.op X4 (M.op X5 X4)) X0)) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq136 (M.op (M.op X2 (M.op (M.op X3 X0) X3)) X2) x X1 X1 X4 X5
       have i₂ := eq134 X2 X3 X0 X1 x
       grind)
    | exact superpose eq134 eq136
    | exact resolve eq136 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq136
  have eq13928 : ∀ X0 X3 X4 X5 : G, (M.op (M.op (M.op X3 X0) X3) (M.op (M.op X4 (M.op X5 X4)) X0)) = X5 := by
    intro X0 X3 X4 X5
    first
    | (have i₁ := eq13592 X0 x x X3 X4 X5
       have i₂ := eq2379 x (M.op (M.op X3 X0) X3) x
       grind)
    | exact superpose eq2379 eq13592
    | exact resolve eq13592 eq2379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2379 eq13592
  have eq42988 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op x (M.op x x)) X1)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq13928 X1 X0 x y
       have i₂ := eq546
       grind)
    | exact superpose eq546 eq13928
    | exact resolve eq13928 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq42991 : x = y ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq42988 x x
       have i₂ := eq13928 x x x x
       grind)
    | (have i₁ := eq42988 x x
       have i₂ := eq13928 x x x (M.op (M.op (M.op x x) x) (M.op (M.op x (M.op x x)) x))
       grind)
    | exact superpose eq13928 eq42988
    | exact resolve eq42988 eq13928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13928 eq42988
  have eq43027 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq42991
       grind)
    | exact superpose eq42991 eq16
    | exact resolve eq16 eq42991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42991
  have eq43028 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq43027
       have r₂ := eq95 x
       grind)
    | exact resolve eq43027 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43027
  have eq43198 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op X0 (M.op (σ (M.op x x)) X0))) := by
    intro X0
    first
    | (have i₁ := eq116 (σ y) (σ x) X0
       have i₂ := eq43028
       grind)
    | exact superpose eq43028 eq116
    | exact resolve eq116 eq43028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq43028
  have eq43292 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq43198 x
       have i₂ := eq387 x x
       grind)
    | exact superpose eq387 eq43198
    | exact resolve eq43198 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387 eq43198
  have eq43364 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq43292
       grind)
    | exact superpose eq43292 eq10
    | exact resolve eq10 eq43292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43292
  have eq43420 : x = y := by
    first
    | (have i₁ := eq43364
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq43364
    | exact resolve eq43364 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43364
  have eq45129 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq43420
       grind)
    | exact superpose eq43420 eq16
    | exact resolve eq16 eq43420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43420
  have eq45132 : False := by grind
  exact eq45132

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pyx_pxx_pxy_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq14 X0 (M.op X1 (M.op X2 X1)) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y x) ∨ y = (M.op y y) := by
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
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq78
    | exact resolve eq78 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq84 : (M.op x x) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq83
    | exact resolve eq83 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq96 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq104 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq104 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq104 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq104 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq107 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq105 (σ X0)
       grind)
    | exact superpose eq105 eq10
    | exact resolve eq10 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq105 sF2
       grind)
    | exact superpose eq105 eq49
    | exact resolve eq49 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq111 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq110
       have i₂ := eq105 x
       grind)
    | exact superpose eq105 eq110
    | exact resolve eq110 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq114 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq107 X0
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq107
    | exact resolve eq107 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq119 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq96
       have i₂ := eq105 sF3
       grind)
    | exact superpose eq105 eq96
    | exact resolve eq96 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq120 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq119
       have i₂ := eq105 y
       grind)
    | exact superpose eq105 eq119
    | exact resolve eq119 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq119
  have eq129 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  clear eq37
  have eq249 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 (M.op X1 X0)) (M.op y (M.op x y)))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq434 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (σ x))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op (σ y) (M.op (σ x) (σ y)))))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq442 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) (M.op X3 (M.op X1 X3))) = (M.op (M.op X4 X0) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X1 X4 (M.op X1 (M.op X2 (M.op X0 X2))) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq449 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X3 X2))) = (M.op X0 (M.op (M.op X1 X3) (M.op X4 (M.op X0 X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X3 (M.op (M.op X1 X3) (M.op X4 (M.op X0 X4))) X1 X2
       have i₂ := eq14 X0 (M.op X1 X3) X4
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq453 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 X1) x X1 X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq458 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X0) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 x
       have i₂ := eq52 X2 X0 X1 x
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0)) X3) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3 (M.op X1 X2)
       have i₂ := eq52 X1 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X1))) (M.op (M.op X3 (M.op X4 X3)) (M.op X0 X2))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X4 (M.op (M.op X3 (M.op X4 X3)) (M.op X0 X2)) X3
       have i₂ := eq52 X2 (M.op X3 (M.op X4 X3)) X0 X1
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq474 : ∀ X0 X1 X2 : G, (σ x) = (M.op (M.op X0 (M.op X1 (M.op X2 X1))) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op (M.op sF3 sF4) (M.op X2 X0))
       have i₂ := eq52 X0 (M.op sF3 sF4) X2 x
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) (M.op X4 (M.op X3 X4)))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X3 (M.op X1 X2) X2 X4
       have i₂ := eq52 X1 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq508 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op y (M.op x y))) (M.op (M.op X1 (M.op X2 X1)) (M.op X0 x))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq53
    | exact resolve eq53 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq114 X0
       grind)
    | exact superpose eq114 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq1044 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq453 X2 (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq453
    | exact resolve eq453 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1046 : ∀ X0 : G, (M.op (M.op y (M.op x y)) (M.op X0 x)) = X0 := by
    intro X0
    first
    | exact superpose eq50 eq453
    | exact resolve eq453 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1047 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op X0 (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq453
    | exact resolve eq453 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1049 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 (M.op (M.op X0 (M.op X3 X1)) X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq453 X3 X1 (M.op X2 (M.op (M.op X0 (M.op X3 X1)) X2))
       have i₂ := eq453 X0 (M.op X3 X1) X2
       grind)
    | exact superpose eq453 eq453
    | exact resolve eq453 eq453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1071 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 x) X0)) := by
    intro X0
    first
    | exact superpose eq1046 eq453
    | exact resolve eq453 eq1046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046
  have eq1141 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq1047 eq453
    | exact resolve eq453 eq1047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047
  have eq1199 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 y) X0) := by
    intro X0
    first
    | exact superpose eq1071 eq14
    | exact resolve eq14 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071
  have eq1220 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq1141 eq14
    | exact resolve eq14 eq1141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq1235 : (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) (M.op y y)) := by
    first
    | (have i₁ := eq1199 (M.op y y)
       have i₂ := eq1199 y
       grind)
    | exact superpose eq1199 eq1199
    | exact resolve eq1199 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1237 : ∀ X0 : G, (M.op y (M.op X0 (M.op (M.op x y) x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq453 X0 y X0
       have i₂ := eq1199 X0
       grind)
    | (have i₁ := eq453 x y x
       have i₂ := eq1199 X0
       grind)
    | exact superpose eq1199 eq453
    | exact resolve eq453 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199
  have eq1327 : ∀ X0 : G, (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x)))) = X0 := by
    intro X0
    first
    | exact superpose eq1220 eq453
    | exact resolve eq453 eq1220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220
  have eq1512 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X1) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq453 X2 (M.op X1 X2) (M.op X0 X1)
       have i₂ := eq1044 X1 X2 X0
       grind)
    | exact superpose eq1044 eq453
    | exact resolve eq453 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1519 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1237 (M.op x (M.op x x))
       have i₂ := eq1044 x x sF0
       grind)
    | exact superpose eq1044 eq1237
    | exact resolve eq1237 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237
  have eq1521 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq1327 (M.op x (M.op sF2 x))
       have i₂ := eq1044 sF2 x sF4
       grind)
    | exact superpose eq1044 eq1327
    | exact resolve eq1327 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044 eq1327
  have eq1581 : ∀ X0 X1 : G, (M.op y (M.op x y)) = (M.op (M.op X0 x) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq249 eq458
    | exact resolve eq458 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq1950 : ∀ X0 : G, (M.op (M.op (M.op y (M.op x y)) X0) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq458 X0 x X0
       have i₂ := eq1519 X0
       grind)
    | (have i₁ := eq458 y x y
       have i₂ := eq1519 X0
       grind)
    | exact superpose eq1519 eq458
    | exact resolve eq458 eq1519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1519
  have eq2001 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq1521 eq458
    | exact resolve eq458 eq1521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458 eq1521
  have eq3024 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X1) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq453 X2 X0 (M.op (M.op X1 X2) X1)
       have i₂ := eq1512 X1 X2 X0
       grind)
    | exact superpose eq1512 eq453
    | exact resolve eq453 eq1512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453 eq1512
  have eq9703 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq434 (M.op X1 (M.op x X1)) sF4 sF3
       have i₂ := eq53 sF3 X1 x sF4
       grind)
    | exact superpose eq53 eq434
    | exact resolve eq434 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq434
  have eq15284 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) X1) (M.op X0 (M.op y (M.op x y)))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq508 eq459
    | exact resolve eq459 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459 eq508
  have eq18322 : ∀ X0 X1 X2 X3 : G, (σ x) = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (M.op X2 (M.op X3 (M.op X1 X3))) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq474 (M.op X2 (M.op X3 (M.op X1 X3))) x X2
       have i₂ := eq442 X1 X2 X3 x X0
       grind)
    | exact superpose eq442 eq474
    | exact resolve eq474 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq18578 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op (σ y) (M.op (σ x) (σ y))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18322 X0 X1 x x
       have i₂ := eq14 X1 x x
       grind)
    | exact superpose eq14 eq18322
    | exact resolve eq18322 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18322
  have eq21256 : ∀ X0 X1 X2 X3 X5 X6 : G, (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X5 (M.op X6 X5)) (M.op (M.op X2 (M.op X3 (M.op X1 X3))) X2))) = X6 := by
    intro X0 X1 X2 X3 X5 X6
    first
    | (have i₁ := eq472 (M.op X2 (M.op X3 (M.op X1 X3))) x X2 X5 X6
       have i₂ := eq442 X1 X2 X3 x X0
       grind)
    | exact superpose eq442 eq472
    | exact resolve eq472 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442 eq472
  have eq21965 : ∀ X0 X1 X5 X6 : G, (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X5 (M.op X6 X5)) X1)) = X6 := by
    intro X0 X1 X5 X6
    first
    | (have i₁ := eq21256 X0 X1 x x X5 X6
       have i₂ := eq14 X1 x x
       grind)
    | exact superpose eq14 eq21256
    | exact resolve eq21256 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21256
  have eq97093 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op (M.op x y) x) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq15284 eq449
    | exact resolve eq449 eq15284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449 eq15284
  have eq102824 : ∀ X0 X1 : G, (M.op y (M.op x y)) = (M.op (M.op (M.op (M.op X0 X1) X0) x) (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) X1) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq18578 eq1581
    | exact resolve eq1581 eq18578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1581 eq18578
  have eq102863 : ∀ X0 X1 : G, (M.op y (M.op x y)) = (M.op (M.op (M.op (M.op X0 X1) X0) x) X1) := by
    intro X0 X1
    first
    | exact superpose eq2001 eq102824
    | exact resolve eq102824 eq2001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2001 eq102824
  have eq138150 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X0 X1)) (σ y))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq9703 eq1049
    | exact resolve eq1049 eq9703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049 eq9703
  have eq429816 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op x (M.op x x)) X1)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq21965 X0 X1 x y
       have i₂ := eq84
       grind)
    | exact superpose eq84 eq21965
    | exact resolve eq21965 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq429889 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq429816 x x
       have i₂ := eq21965 x x x x
       grind)
    | (have i₁ := eq429816 x x
       have i₂ := eq21965 x x x (M.op (M.op (M.op x x) x) (M.op (M.op x (M.op x x)) x))
       grind)
    | exact superpose eq21965 eq429816
    | exact resolve eq429816 eq21965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21965 eq429816
  have eq459715 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq429889 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq429889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429889
  have eq459716 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq459715
    | exact resolve eq459715 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459715
  have eq459727 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq459716
       have r₂ := eq27
       grind)
    | exact resolve eq459716 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459716
  have eq459985 : (σ y) = (M.op (σ x) (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ x))) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq459727 eq138150
    | exact resolve eq138150 eq459727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459727
  have eq459995 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq138150 eq459985
    | exact resolve eq459985 eq138150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138150 eq459985
  have eq460330 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq459995 eq120
    | exact resolve eq120 eq459995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq459995
  have eq460707 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq460330
    | exact resolve eq460330 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460330
  have eq460708 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq460707
  have eq460805 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq460708
       grind)
    | exact superpose eq460708 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq460708
       grind)
    | exact resolve eq13 eq460708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq460810 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq696 y X0
       have i₂ := eq460708
       grind)
    | exact superpose eq460708 eq696
    | (have j0 := eq696 y X0
       grind)
    | exact resolve eq696 eq460708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq461013 : y = (M.op (M.op (M.op x y) x) (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq97093 y y
       have i₂ := eq460708
       grind)
    | exact superpose eq460708 eq97093
    | exact resolve eq97093 eq460708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97093 eq460708
  have eq461034 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq460810 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460810
  have eq461035 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq460805 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460805
  have eq461044 : y = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1235 eq461013
    | exact resolve eq461013 eq1235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1235 eq461013
  have eq461131 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq461034 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq461034
    | (have j0 := eq461034 X0
       grind)
    | exact resolve eq461034 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461034
  have eq463876 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) (M.op x y))) = X2 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1 X2
    first
    | exact superpose eq461044 eq503
    | exact resolve eq503 eq461044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq464022 : (M.op y (M.op x y)) = (M.op (M.op (M.op y (M.op x y)) x) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq461044 eq102863
    | exact resolve eq102863 eq461044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102863 eq461044
  have eq464048 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1950 eq464022
    | exact resolve eq464022 eq1950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1950 eq464022
  have eq464161 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) (M.op x y))) = X2 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq463876 X0 X1 X2
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq463876
    | (have j0 := eq463876 X0 X1 X2
       grind)
    | exact resolve eq463876 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463876
  have eq464308 : ∀ X1 X2 : G, (M.op (M.op X1 X2) X1) = X2 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1 X2
    first
    | (have i₁ := eq464161 X1 X1 X2
       have i₂ := eq3024 sF0 X1 (M.op (M.op X1 X2) X1)
       grind)
    | exact superpose eq3024 eq464161
    | exact resolve eq464161 eq3024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3024 eq464161
  have eq487914 : (σ (M.op y (M.op x y))) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq129
       have i₂ := eq461035 sF0
       grind)
    | exact superpose eq461035 eq129
    | exact resolve eq129 eq461035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq461035
  have eq873474 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq464048 eq487914
    | exact resolve eq487914 eq464048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464048 eq487914
  have eq873573 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq873474
  have eq873582 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq873573
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq873573
    | exact resolve eq873573 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873573
  have eq873594 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq873582 eq461131
    | exact resolve eq461131 eq873582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461131 eq873582
  have eq873596 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq873594
  have eq873929 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq873596 eq464308
    | exact resolve eq464308 eq873596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464308 eq873596
  have eq873932 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq873929
  have eq873934 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq873932
    | exact resolve eq873932 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873932
  have eq874094 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq873934
       have r₂ := eq27
       grind)
    | exact resolve eq873934 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873934
  have eq874159 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq874094 eq29
    | exact resolve eq29 eq874094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq874094
  have eq874552 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq874159
    | exact resolve eq874159 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq874159
  have eq874553 : x = y := by grind
  clear eq874552
  have eq874584 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq874553
       grind)
    | exact superpose eq874553 eq18
    | exact resolve eq18 eq874553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq874585 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq874553
       grind)
    | exact superpose eq874553 eq24
    | exact resolve eq24 eq874553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq874553
  have eq874992 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq874585
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq874585
    | exact resolve eq874585 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq874585
  have eq875058 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq874992 eq26
    | exact resolve eq26 eq874992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq874992
  have eq876521 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq875058 eq111
    | exact resolve eq111 eq875058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq875058
  have eq877236 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq876521
       have i₂ := eq874584
       grind)
    | exact superpose eq874584 eq876521
    | exact resolve eq876521 eq874584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874584 eq876521
  have eq877488 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq877236 eq15
    | exact resolve eq15 eq877236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877236
  have eq877570 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq877488
    | exact resolve eq877488 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq877488
  have eq877591 : False := by grind
  exact eq877591

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pyx_pyy_pyx_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 (M.op X0 X1) x X1 X2
       have i₂ := eq9 X0 x X1
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0)) X3) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X3 (M.op X1 X2)
       have i₂ := eq61 X1 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq672 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq673 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq672 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq672 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq672 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq682 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq673 (σ X0)
       grind)
    | exact superpose eq673 eq15
    | exact resolve eq15 eq673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq682 X0
       have i₂ := eq673 X0
       grind)
    | exact superpose eq673 eq682
    | exact resolve eq682 eq673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673 eq682
  have eq727 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) = (M.op (M.op X2 (M.op X1 (σ X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 (σ X0) X2 X1 (σ X0)
       have i₂ := eq697 X0
       grind)
    | exact superpose eq697 eq61
    | exact resolve eq61 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq731 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op X1 (M.op (σ (M.op X0 X0)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq76 (σ X0) (σ X0) X1
       have i₂ := eq697 X0
       grind)
    | exact superpose eq697 eq76
    | exact resolve eq76 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1013 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1022 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1013 (σ X1) (σ X0)
       grind)
    | exact superpose eq1013 eq15
    | (have j1 := eq1013 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1035 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1022 X0 X1
       have i₂ := eq697 X1
       grind)
    | exact superpose eq697 eq1022
    | (have j0 := eq1022 X0 X1
       grind)
    | exact resolve eq1022 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq1381 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1035 X0 X1
       have i₂ := eq1013 X1 X0
       grind)
    | exact superpose eq1013 eq1035
    | (have j0 := eq1035 X0 X1
       have j1 := eq1013 X1 X0
       grind)
    | exact resolve eq1035 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013 eq1035
  have eq3025 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X2 X0) X2)) X1) (M.op X3 X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq76 X3 (M.op (M.op X1 (M.op (M.op X2 X0) X2)) X1) X3
       have i₂ := eq80 X1 X2 X0 X3
       grind)
    | exact superpose eq80 eq76
    | exact resolve eq76 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq82792 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (σ X0) (M.op X1 (M.op (σ (M.op X0 X0)) X1))) ∨ (M.op (σ X2) (σ X0)) = (σ (M.op X2 X0)) ∨ (M.op X0 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76 (σ X2) (σ X0) X1
       have i₂ := eq1381 X2 X0
       grind)
    | exact superpose eq1381 eq76
    | (have j1 := eq1381 X2 X0
       grind)
    | exact resolve eq76 eq1381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq1381
  have eq82945 : ∀ X0 X2 : G, (M.op (σ X2) (σ X0)) = (σ (M.op X2 X0)) ∨ (σ X0) = (σ X2) ∨ (M.op X0 X0) = (M.op X2 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq82792 X0 x X2
       have i₂ := eq731 X0 x
       grind)
    | exact superpose eq731 eq82792
    | (have j0 := eq82792 X0 x X2
       grind)
    | exact resolve eq82792 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731 eq82792
  have eq87756 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op (σ X0) X1) (M.op (σ X0) (σ (M.op X0 X0)))) (M.op X3 X1)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq3025 X1 x (σ X0) X3
       have i₂ := eq727 X0 (M.op (σ X0) X1) x
       grind)
    | exact superpose eq727 eq3025
    | exact resolve eq3025 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727 eq3025
  have eq1259995 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq82945 y x
       grind)
    | exact superpose eq82945 eq16
    | (have j1 := eq82945 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq82945 y x
       grind)
    | exact resolve eq16 eq82945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82945
  have eq1260605 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq1259995
  have eq1261440 : ∀ X0 : G, y = (M.op (M.op (M.op (σ X0) y) (M.op (σ X0) (σ (M.op X0 X0)))) (M.op x y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq87756 X0 y y
       have i₂ := eq1260605
       grind)
    | exact superpose eq1260605 eq87756
    | exact resolve eq87756 eq1260605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260605
  have eq1261453 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1261440 x
       have i₂ := eq87756 x y x
       grind)
    | (have i₁ := eq1261440 x
       have i₂ := eq87756 x x (M.op (M.op (M.op (σ x) y) (M.op (σ x) (σ (M.op x x)))) (M.op x y))
       grind)
    | exact superpose eq87756 eq1261440
    | exact resolve eq1261440 eq87756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87756 eq1261440
  have eq1261531 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1261453
       grind)
    | exact superpose eq1261453 eq10
    | exact resolve eq10 eq1261453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261453
  have eq1261815 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1261531
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1261531
    | exact resolve eq1261531 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261531
  have eq1261816 : x = y := by grind
  clear eq1261815
  have eq1261819 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1261816
       grind)
    | exact superpose eq1261816 eq16
    | exact resolve eq16 eq1261816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261816
  have eq1261820 : False := by grind
  exact eq1261820

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pyx_pyy_pxy_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq14 X0 (M.op X1 (M.op X2 X1)) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
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
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq78
    | exact resolve eq78 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq83
    | exact resolve eq83 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq85
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq85
    | exact resolve eq85 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq97 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq105 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq105 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq105 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq110 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq106 y
       grind)
    | exact superpose eq106 eq70
    | exact resolve eq70 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq111 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq106 sF2
       grind)
    | exact superpose eq106 eq49
    | exact resolve eq49 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq112 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq111
       have i₂ := eq106 x
       grind)
    | exact superpose eq106 eq111
    | exact resolve eq111 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq113 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq110
       have i₂ := eq106 sF3
       grind)
    | exact superpose eq106 eq110
    | exact resolve eq110 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq119 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq97
       have i₂ := eq106 sF3
       grind)
    | exact superpose eq106 eq97
    | exact resolve eq97 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq120 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq119
       have i₂ := eq106 y
       grind)
    | exact superpose eq106 eq119
    | exact resolve eq119 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq119
  have eq129 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  clear eq37
  have eq433 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 x)) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op y (M.op x y))))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq453 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 X1) x X1 X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq455 : ∀ X0 : G, x = (M.op y (M.op X0 (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq456 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq461 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op (M.op X4 (M.op X2 X4)) (M.op (M.op X0 (M.op X1 X2)) X0))) X3) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X1 X3 (M.op X4 (M.op X2 X4))
       have i₂ := eq52 X2 X0 X1 X4
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq509 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (M.op X1 (M.op X2 X1)) (M.op X0 (σ x)))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq521 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X2 (M.op (M.op (M.op X3 (M.op X0 X3)) (M.op X4 (M.op X1 X4))) X2))) = (M.op (M.op X5 X0) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 (M.op (M.op X3 (M.op X0 X3)) (M.op X4 (M.op X1 X4))) X5 X1 X2
       have i₂ := eq53 X1 X3 X0 X4
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1046 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq453 X2 (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq453
    | exact resolve eq453 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1049 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op X0 (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq453
    | exact resolve eq453 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1135 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq1049 eq453
    | exact resolve eq453 eq1049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049
  have eq1214 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq1135 eq14
    | exact resolve eq14 eq1135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq1317 : ∀ X0 : G, (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x)))) = X0 := by
    intro X0
    first
    | exact superpose eq1214 eq453
    | exact resolve eq453 eq1214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1537 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y X0)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1046 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1046
    | (have j0 := eq1046 y X0 x
       grind)
    | exact resolve eq1046 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1563 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq1317 (M.op x (M.op sF2 x))
       have i₂ := eq1046 sF2 x sF4
       grind)
    | exact superpose eq1046 eq1317
    | exact resolve eq1317 eq1046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046 eq1317
  have eq1998 : x = (M.op y (M.op (M.op (σ x) (M.op x y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq1563 eq455
    | exact resolve eq455 eq1563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq2001 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq1563 eq456
    | exact resolve eq456 eq1563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456 eq1563
  have eq8746 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq433 (M.op X1 (M.op x X1)) sF0 y
       have i₂ := eq53 y X1 x sF0
       grind)
    | exact superpose eq53 eq433
    | exact resolve eq433 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq433
  have eq19465 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (M.op X1 X0)) (M.op (σ y) (M.op (σ x) (σ y))))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq509 eq461
    | exact resolve eq461 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461 eq509
  have eq123846 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq86 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq123853 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq123846
    | exact resolve eq123846 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123846
  have eq123864 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq123853
       have r₂ := eq27
       grind)
    | exact resolve eq123853 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123853
  have eq123868 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq123864
    | exact resolve eq123864 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123864
  have eq124006 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq123868 eq19465
    | exact resolve eq19465 eq123868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123868
  have eq124011 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2001 eq124006
    | exact resolve eq124006 eq2001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2001 eq124006
  have eq124049 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq124011 eq120
    | exact resolve eq120 eq124011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq124011
  have eq124219 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq124049
    | exact resolve eq124049 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124049
  have eq124220 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq124219
  have eq124664 : y = (M.op y (M.op (M.op (σ x) (M.op x y)) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq19465 y y
       have i₂ := eq124220
       grind)
    | exact superpose eq124220 eq19465
    | exact resolve eq19465 eq124220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19465 eq124220
  have eq124669 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1998 eq124664
    | exact resolve eq124664 eq1998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1998 eq124664
  have eq124724 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq113
       have i₂ := eq124669
       grind)
    | exact superpose eq124669 eq113
    | exact resolve eq113 eq124669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq124738 : x = (M.op (M.op y y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1537 y
       have i₂ := eq124669
       grind)
    | exact superpose eq124669 eq1537
    | exact resolve eq1537 eq124669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537
  have eq124740 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq124669
       grind)
    | exact superpose eq124669 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq124669
       grind)
    | exact resolve eq13 eq124669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124858 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq124740 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124740
  have eq124896 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq124724
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq124724
    | exact resolve eq124724 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124724
  have eq125234 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq124896 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq124896
       grind)
    | exact resolve eq13 eq124896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124896
  have eq125352 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq125234 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125234
  have eq125890 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq124738
       have i₂ := eq124669
       grind)
    | exact superpose eq124669 eq124738
    | exact resolve eq124738 eq124669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124669 eq124738
  have eq126027 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq125890
  have eq126225 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) X3) = (M.op y (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X1)) (M.op (M.op x y) x)) X0))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq126027 eq521
    | exact resolve eq521 eq126027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq126293 : ∀ X0 X2 X3 : G, (M.op (M.op X3 X2) X3) = (M.op y (M.op X0 (M.op (M.op X2 y) X0))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X2 X3
    first
    | exact superpose eq8746 eq126225
    | exact resolve eq126225 eq8746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8746 eq126225
  have eq126372 : ∀ X2 X3 : G, (M.op (M.op X3 X2) X3) = X2 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X2 X3
    first
    | (have i₁ := eq126293 x X2 X3
       have i₂ := eq453 X2 y x
       grind)
    | exact superpose eq453 eq126293
    | exact resolve eq126293 eq453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453 eq126293
  have eq129081 : (σ (M.op y (M.op x y))) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq129
       have i₂ := eq124858 sF0
       grind)
    | exact superpose eq124858 eq129
    | exact resolve eq129 eq124858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq124858
  have eq217717 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq126027 eq129081
    | exact resolve eq129081 eq126027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126027 eq129081
  have eq217794 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq217717
  have eq217800 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq217794
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq217794
    | exact resolve eq217794 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217794
  have eq217812 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq217800 eq125352
    | exact resolve eq125352 eq217800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125352 eq217800
  have eq217820 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq217812
  have eq217998 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq217820 eq126372
    | exact resolve eq126372 eq217820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126372 eq217820
  have eq217999 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq217998
  have eq218001 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq217999
    | exact resolve eq217999 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217999
  have eq218069 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq218001
       have r₂ := eq27
       grind)
    | exact resolve eq218001 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218001
  have eq218076 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq218069 eq29
    | exact resolve eq29 eq218069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq218069
  have eq218314 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq218076
    | exact resolve eq218076 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq218076
  have eq218315 : x = y := by grind
  clear eq218314
  have eq218337 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq218315
       grind)
    | exact superpose eq218315 eq18
    | exact resolve eq18 eq218315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq218338 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq218315
       grind)
    | exact superpose eq218315 eq24
    | exact resolve eq24 eq218315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq218315
  have eq218577 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq218338
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq218338
    | exact resolve eq218338 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq218338
  have eq218610 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq218577 eq26
    | exact resolve eq26 eq218577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq218577
  have eq219400 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq218610 eq112
    | exact resolve eq112 eq218610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq218610
  have eq219743 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq219400
       have i₂ := eq218337
       grind)
    | exact superpose eq218337 eq219400
    | exact resolve eq219400 eq218337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218337 eq219400
  have eq219851 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq219743 eq15
    | exact resolve eq15 eq219743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219743
  have eq219935 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq219851
    | exact resolve eq219851 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq219851
  have eq219956 : False := by grind
  exact eq219956

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pxy_pxx_pxy_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq14 X0 (M.op X1 (M.op X2 X1)) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) := by
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
  clear eq44
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq95
    | exact resolve eq95 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq103 : (M.op y x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq101
    | exact resolve eq101 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
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
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq112 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq118 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq113 sF2
       grind)
    | exact superpose eq113 eq49
    | exact resolve eq49 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq121 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq118
       have i₂ := eq113 x
       grind)
    | exact superpose eq113 eq118
    | exact resolve eq118 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq118
  have eq447 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 X1) x X1 X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq498 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) (M.op X4 (M.op X3 X4)))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X3 (M.op X1 X2) X2 X4
       have i₂ := eq52 X1 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq53
  have eq1079 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq447 X2 (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq447
    | exact resolve eq447 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1533 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X1) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq447 X2 (M.op X1 X2) (M.op X0 X1)
       have i₂ := eq1079 X1 X2 X0
       grind)
    | exact superpose eq1079 eq447
    | exact resolve eq447 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079
  have eq3016 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X1) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq447 X2 X0 (M.op (M.op X1 X2) X1)
       have i₂ := eq1533 X1 X2 X0
       grind)
    | exact superpose eq1533 eq447
    | exact resolve eq447 eq1533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447 eq1533
  have eq29391 : ∀ X0 X1 X2 : G, y = (M.op X0 (M.op (M.op (M.op X1 (M.op (M.op y x) y)) X1) (M.op X2 (M.op X0 X2)))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq498 X1 y y X0 X2
       have i₂ := eq103
       grind)
    | exact superpose eq103 eq498
    | exact resolve eq498 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq29417 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq29391 x x x
       have i₂ := eq498 x y x x x
       grind)
    | exact superpose eq498 eq29391
    | exact resolve eq29391 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498 eq29391
  have eq29436 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq29417 eq72
    | (have j0 := eq72 (σ x) (σ y)
       grind)
    | exact resolve eq72 eq29417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq29417
  have eq29437 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq26 eq29436
    | exact resolve eq29436 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29436
  have eq29440 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq29437
       have r₂ := eq27
       grind)
    | exact resolve eq29437 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29437
  have eq31377 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op (M.op (σ y) (σ x)) (σ y)) X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq29440 eq3016
    | exact resolve eq3016 eq29440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29440
  have eq31387 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq31377 x
       have i₂ := eq3016 x sF3 sF2
       grind)
    | exact superpose eq3016 eq31377
    | exact resolve eq31377 eq3016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3016 eq31377
  have eq31408 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq31387 eq29
    | exact resolve eq29 eq31387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq31387
  have eq31492 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq31408
    | exact resolve eq31408 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq31408
  have eq31493 : x = y := by grind
  clear eq31492
  have eq31498 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq31493
       grind)
    | exact superpose eq31493 eq18
    | exact resolve eq18 eq31493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq31499 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq31493
       grind)
    | exact superpose eq31493 eq24
    | exact resolve eq24 eq31493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq31493
  have eq31602 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq31499
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31499
    | exact resolve eq31499 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq31499
  have eq31612 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq31602 eq26
    | exact resolve eq26 eq31602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq31602
  have eq31876 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq31612 eq121
    | exact resolve eq121 eq31612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq31612
  have eq31994 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq31876
       have i₂ := eq31498
       grind)
    | exact superpose eq31498 eq31876
    | exact resolve eq31876 eq31498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31498 eq31876
  have eq34728 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31994 eq15
    | exact resolve eq15 eq31994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31994
  have eq34772 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq34728
    | exact resolve eq34728 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq34728
  have eq34781 : False := by grind
  exact eq34781

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pxy_pxx_pyx_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq14 X0 (M.op X1 (M.op X2 X1)) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq82 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq69
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq69 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq88 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq82
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq82
    | exact resolve eq82 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq88
    | exact resolve eq88 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq89
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq89
    | exact resolve eq89 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq104 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq104 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq104 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq104 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq108 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq105 x
       grind)
    | exact superpose eq105 eq43
    | exact resolve eq43 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq110 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq105 sF2
       grind)
    | exact superpose eq105 eq49
    | exact resolve eq49 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq111 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq110
       have i₂ := eq105 x
       grind)
    | exact superpose eq105 eq110
    | exact resolve eq110 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq113 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq105 sF2
       grind)
    | exact superpose eq105 eq108
    | exact resolve eq108 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq108
  have eq129 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  clear eq37
  have eq247 : x = (M.op x (M.op (M.op y (M.op x y)) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq442 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X0 X2)) (M.op X4 (M.op X3 X4))) = (M.op (M.op X5 (M.op X0 (M.op X1 (M.op X2 X1)))) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 X3 X5 (M.op X3 (M.op X0 X2)) X4
       have i₂ := eq52 X2 X3 X0 X1
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq445 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op y X0))) = (M.op (M.op X1 (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 y X1 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 y X1 x X0
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 (M.op (σ y) X0))) = (M.op (M.op X1 (M.op (σ x) (σ y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ y) X1 (σ x) X0
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 X1) x X1 X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X0) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 x
       have i₂ := eq52 X2 X0 X1 x
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1054 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq452 X2 (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq452
    | exact resolve eq452 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1056 : ∀ X0 : G, (M.op (M.op y (M.op x y)) (M.op X0 x)) = X0 := by
    intro X0
    first
    | exact superpose eq50 eq452
    | exact resolve eq452 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1057 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op X0 (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq452
    | exact resolve eq452 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1078 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 x) X0)) := by
    intro X0
    first
    | exact superpose eq1056 eq452
    | exact resolve eq452 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1091 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq1057 eq452
    | exact resolve eq452 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq1109 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 y) X0) := by
    intro X0
    first
    | exact superpose eq1078 eq14
    | exact resolve eq14 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078
  have eq1126 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op (M.op X1 X0) X1) (M.op y (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq1056 eq457
    | exact resolve eq457 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056
  have eq1131 : ∀ X0 : G, y = (M.op (M.op (M.op X0 (M.op x y)) X0) x) := by
    intro X0
    first
    | (have i₁ := eq457 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq457
    | (have j0 := eq457 X0 x y
       grind)
    | exact resolve eq457 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1136 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq457
    | (have j0 := eq457 X0 (σ x) (σ y)
       grind)
    | exact resolve eq457 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1149 : (M.op y (M.op x y)) = (M.op (M.op x x) (M.op y (M.op x y))) := by
    first
    | exact superpose eq247 eq457
    | exact resolve eq457 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq457
  have eq1221 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq1091 eq14
    | exact resolve eq14 eq1091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
  have eq1239 : ∀ X0 : G, (M.op y (M.op X0 (M.op (M.op x y) x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq452 X0 y X0
       have i₂ := eq1109 X0
       grind)
    | (have i₁ := eq452 x y x
       have i₂ := eq1109 X0
       grind)
    | exact superpose eq1109 eq452
    | exact resolve eq452 eq1109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1493 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y X0)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1054 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1054
    | (have j0 := eq1054 y X0 x
       grind)
    | exact resolve eq1054 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1539 : ∀ X0 : G, (M.op (M.op y X0) (M.op (M.op x y) x)) = X0 := by
    intro X0
    first
    | exact superpose eq1493 eq452
    | exact resolve eq452 eq1493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452 eq1493
  have eq33090 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op x y)) X0) x) = (M.op (M.op X1 (M.op (M.op X2 y) X2)) (M.op X3 (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq442 (M.op X2 y) y X2 X1 X3 x
       have i₂ := eq445 (M.op X2 y) X0
       grind)
    | exact superpose eq445 eq442
    | exact resolve eq442 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq33093 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) X0) (σ x)) = (M.op (M.op X1 (M.op (M.op X2 (σ y)) X2)) (M.op X3 (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq446 eq442
    | exact resolve eq442 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442 eq446
  have eq33576 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) X0) (σ x)) = (M.op (M.op X1 (M.op (M.op (σ x) (σ y)) (σ x))) (M.op X3 (M.op X1 X3))) := by
    intro X0 X1 X3
    first
    | exact superpose eq1221 eq33093
    | (have j0 := eq33093 X0 X1 (σ x) X3
       grind)
    | exact resolve eq33093 eq1221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221 eq33093
  have eq33579 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 (M.op x y)) X0) x) = (M.op (M.op X1 (M.op (M.op x y) x)) (M.op X3 (M.op X1 X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq33090 X0 X1 x X3
       have i₂ := eq1109 x
       grind)
    | (have i₁ := eq33090 X0 X1 x X3
       have i₂ := eq1109 X0
       grind)
    | exact superpose eq1109 eq33090
    | (have j0 := eq33090 X0 X1 x X3
       grind)
    | exact resolve eq33090 eq1109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109 eq33090
  have eq33905 : ∀ X1 X3 : G, (σ y) = (M.op (M.op X1 (M.op (M.op (σ x) (σ y)) (σ x))) (M.op X3 (M.op X1 X3))) := by
    intro X1 X3
    first
    | exact superpose eq1136 eq33576
    | exact resolve eq33576 eq1136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136 eq33576
  have eq33906 : ∀ X1 X3 : G, y = (M.op (M.op X1 (M.op (M.op x y) x)) (M.op X3 (M.op X1 X3))) := by
    intro X1 X3
    first
    | exact superpose eq1131 eq33579
    | exact resolve eq33579 eq1131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131 eq33579
  have eq125109 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq90 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq125116 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq125109
    | exact resolve eq125109 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125109
  have eq125127 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq125116
       have r₂ := eq27
       grind)
    | exact resolve eq125116 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125116
  have eq125131 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq125127
    | exact resolve eq125127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125127
  have eq125280 : (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq125131 eq33905
    | exact resolve eq33905 eq125131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33905 eq125131
  have eq125285 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq125280
       have i₂ := eq1054 sF4 sF2 sF2
       grind)
    | exact superpose eq1054 eq125280
    | exact resolve eq125280 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125280
  have eq125392 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq125285 eq111
    | exact resolve eq111 eq125285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125285
  have eq125613 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq125392
    | exact resolve eq125392 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125392
  have eq125614 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq125613
  have eq126088 : y = (M.op (M.op x (M.op (M.op x y) x)) (M.op x (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq33906 x x
       have i₂ := eq125614
       grind)
    | exact superpose eq125614 eq33906
    | exact resolve eq33906 eq125614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125614
  have eq126092 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq126088
       have i₂ := eq1054 sF0 x x
       grind)
    | exact superpose eq1054 eq126088
    | exact resolve eq126088 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054 eq126088
  have eq126209 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq113
       have i₂ := eq126092
       grind)
    | exact superpose eq126092 eq113
    | exact resolve eq113 eq126092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq126237 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq126092
       grind)
    | exact superpose eq126092 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq126092
       grind)
    | exact resolve eq13 eq126092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126318 : x = (M.op (M.op x x) (M.op y (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1126 x x
       have i₂ := eq126092
       grind)
    | exact superpose eq126092 eq1126
    | exact resolve eq1126 eq126092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126 eq126092
  have eq126352 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq126237 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126237
  have eq126363 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1149 eq126318
    | exact resolve eq126318 eq1149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149 eq126318
  have eq126428 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq126209
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq126209
    | exact resolve eq126209 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126209
  have eq126848 : ∀ X0 X1 : G, (M.op y (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op x y) x))) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq126363 eq53
    | exact resolve eq53 eq126363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq126958 : y = (M.op (M.op y (M.op (M.op x y) x)) (M.op (M.op x y) x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq126363 eq33906
    | exact resolve eq33906 eq126363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33906 eq126363
  have eq126959 : y = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1539 eq126958
    | exact resolve eq126958 eq1539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1539 eq126958
  have eq127019 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq1239 eq126848
    | exact resolve eq126848 eq1239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239 eq126848
  have eq127113 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq126428 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq126428
       grind)
    | exact resolve eq13 eq126428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126428
  have eq127229 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq127113 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127113
  have eq130782 : (σ (M.op (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq129
       have i₂ := eq126352 sF0
       grind)
    | exact superpose eq126352 eq129
    | exact resolve eq129 eq126352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq126352
  have eq218972 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq126959 eq130782
    | exact resolve eq130782 eq126959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126959 eq130782
  have eq219049 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq218972
  have eq219055 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq219049
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq219049
    | exact resolve eq219049 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219049
  have eq219067 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq219055 eq127229
    | exact resolve eq127229 eq219055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127229 eq219055
  have eq219075 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq219067
  have eq219263 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq219075 eq127019
    | exact resolve eq127019 eq219075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127019 eq219075
  have eq219266 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq219263
  have eq219267 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq219266
    | exact resolve eq219266 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219266
  have eq219396 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq219267
       have r₂ := eq27
       grind)
    | exact resolve eq219267 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219267
  have eq219422 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq219396 eq29
    | exact resolve eq29 eq219396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq219396
  have eq219659 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq219422
    | exact resolve eq219422 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq219422
  have eq219660 : x = y := by grind
  clear eq219659
  have eq219682 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq219660
       grind)
    | exact superpose eq219660 eq18
    | exact resolve eq18 eq219660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq219683 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq219660
       grind)
    | exact superpose eq219660 eq24
    | exact resolve eq24 eq219660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq219660
  have eq219922 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq219683
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq219683
    | exact resolve eq219683 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq219683
  have eq219955 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq219922 eq26
    | exact resolve eq26 eq219922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq219922
  have eq220730 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq219955 eq111
    | exact resolve eq111 eq219955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq219955
  have eq221073 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq220730
       have i₂ := eq219682
       grind)
    | exact superpose eq219682 eq220730
    | exact resolve eq220730 eq219682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219682 eq220730
  have eq221182 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq221073 eq15
    | exact resolve eq15 eq221073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221073
  have eq221266 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq221182
    | exact resolve eq221182 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq221182
  have eq221287 : False := by grind
  exact eq221287

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq21 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq21 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq26 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
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
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq26 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq34 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq41 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq36 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq37 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq37 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq38 X0 X1
       grind)
    | (have r₁ := eq46 X0 X1
       have r₂ := eq38 X0 X1
       grind)
    | exact resolve eq46 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq46
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq49
    | (have j0 := eq49 X0 X1
       grind)
    | exact resolve eq49 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq49
  have eq97 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq101 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq97 X0 X1
       have j1 := eq51 X1 X0
       grind)
    | (have r₁ := eq97 X1 X0
       have r₂ := eq51 X0 X1
       grind)
    | (have r₁ := eq97 X1 X1
       have r₂ := eq51 X1 X1
       grind)
    | exact resolve eq97 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq97
  have eq298 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq101 (σ X1) (σ X0)
       grind)
    | exact superpose eq101 eq15
    | exact resolve eq15 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq305 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq298 X0 X1
       have i₂ := eq101 X1 X0
       grind)
    | exact superpose eq101 eq298
    | exact resolve eq298 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq298
  have eq308 : False := by grind
  exact eq308

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_y_pyx_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq28 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq28 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28
    | (have j0 := eq28 x
       grind)
    | exact resolve eq28 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq37 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq49 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq52 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq9 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 x X0 y
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq9 X0 (M.op X1 (M.op X2 X1)) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, x = (M.op X0 (M.op (M.op y (M.op x y)) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op y sF0) (M.op x (M.op X0 x)))
       have i₂ := eq9 X0 (M.op y sF0) x
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : x = (M.op x (M.op (M.op y (M.op x y)) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, (M.op X1 (M.op y (M.op x y))) = (M.op (M.op X0 (M.op X1 x)) X0) := by
    intro X0 X1
    first
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 (M.op X1 X0)) (M.op y (M.op x y)))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq10
    | exact resolve eq10 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq97 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq97
    | exact resolve eq97 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq328 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = (M.op x (M.op (M.op X0 x) (M.op y (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq52 eq78
    | exact resolve eq78 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq337 : ∀ X0 X1 : G, (M.op X1 (M.op X0 x)) = (M.op x (M.op (M.op X1 (M.op X0 (M.op y (M.op x y)))) (M.op y (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X1 (M.op X1 (M.op X0 x))
       have i₂ := eq78 X1 X0
       grind)
    | exact superpose eq78 eq79
    | exact resolve eq79 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq377 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq48
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq400 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X3 (M.op (M.op X4 (M.op X2 X4)) X3))) = (M.op (M.op X5 (M.op (M.op X0 (M.op X1 X2)) X0)) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 (M.op X4 (M.op X2 X4)) X5 X1 X3
       have i₂ := eq53 X2 X0 X1 X4
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq401 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) (M.op X3 (M.op X1 X3))) = (M.op (M.op X4 X0) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X1 X4 (M.op X1 (M.op X2 (M.op X0 X2))) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq53
    | exact resolve eq53 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 x)) (M.op X2 (M.op X1 X2))) = (M.op (M.op X3 (M.op X0 (M.op y (M.op x y)))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X1 X3 (M.op X1 (M.op X0 x)) X2
       have i₂ := eq78 X1 X0
       grind)
    | exact superpose eq78 eq53
    | exact resolve eq53 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq407 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) X0))) = (M.op (M.op X1 x) X1) := by
    intro X0 X1
    first
    | exact superpose eq77 eq53
    | exact resolve eq53 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 (M.op (σ y) X0))) = (M.op (M.op X1 (M.op (σ x) (σ y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 (σ y) X1 (σ x) X0
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq415 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X3 X2))) = (M.op X0 (M.op (M.op X1 X3) (M.op X4 (M.op X0 X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X3 (M.op (M.op X1 X3) (M.op X4 (M.op X0 X4))) X1 X2
       have i₂ := eq9 X0 (M.op X1 X3) X4
       grind)
    | exact superpose eq9 eq53
    | exact resolve eq53 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq422 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op (M.op X1 (M.op X0 X1)) (M.op X2 (M.op (M.op y (M.op x y)) X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq79 eq53
    | exact resolve eq53 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X2 X1))) = (M.op X0 (M.op X3 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X2 x X0 X1
       have i₂ := eq53 X2 x X0 X3
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X0) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 x
       have i₂ := eq53 X2 X0 X1 x
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X0 X1 X2 X3 : G, (M.op x (M.op (M.op (M.op X3 (M.op X2 X3)) (M.op (M.op X0 (M.op X1 X2)) X0)) (M.op y (M.op x y)))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq79 (M.op X3 (M.op X2 X3)) X1
       have i₂ := eq53 X2 X0 X1 X3
       grind)
    | exact superpose eq53 eq79
    | exact resolve eq79 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq436 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X0) X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 x X0
       have i₂ := eq53 (M.op X2 X0) x X0 X1
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437 : ∀ X0 X1 : G, (M.op X0 (M.op y (M.op x y))) = (M.op X0 (M.op X1 (M.op x X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq78 x X0
       have i₂ := eq53 x x X0 X1
       grind)
    | exact superpose eq53 eq78
    | exact resolve eq78 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq438 : ∀ X0 : G, x = (M.op y (M.op X0 (M.op (M.op x y) X0))) := by
    intro X0
    first
    | (have i₁ := eq52 x
       have i₂ := eq53 sF0 x y x
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq441 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X2)) = (M.op x (M.op (M.op X3 (M.op X0 (M.op X1 (M.op X2 X1)))) (M.op y (M.op x y)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq79 X3 (M.op X3 (M.op X0 X2))
       have i₂ := eq53 X2 X3 X0 X1
       grind)
    | exact superpose eq53 eq79
    | exact resolve eq79 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq444 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X1))) (M.op (M.op X3 (M.op X4 X3)) (M.op X0 X2))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X4 (M.op (M.op X3 (M.op X4 X3)) (M.op X0 X2)) X3
       have i₂ := eq53 X2 (M.op X3 (M.op X4 X3)) X0 X1
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq467 : ∀ X0 X1 X2 : G, (M.op (M.op X2 x) X2) = (M.op y (M.op X0 (M.op (M.op X1 (M.op (M.op x y) X1)) X0))) := by
    intro X0 X1 X2
    first
    | exact superpose eq438 eq53
    | exact resolve eq53 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq472 : ∀ X0 X1 : G, y = (M.op (M.op X0 (M.op (M.op X1 (M.op (M.op x y) X1)) x)) X0) := by
    intro X0 X1
    first
    | exact superpose eq438 eq9
    | exact resolve eq9 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq473 : ∀ X1 : G, y = (M.op (M.op X1 (M.op (M.op x y) X1)) (M.op y (M.op x y))) := by
    intro X1
    first
    | (have i₁ := eq472 x X1
       have i₂ := eq78 x (M.op X1 (M.op sF0 X1))
       grind)
    | exact superpose eq78 eq472
    | exact resolve eq472 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq472
  have eq493 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) X1) (M.op X2 (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq430 X1 (M.op X2 (M.op X3 (M.op X0 X3))) X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq430
    | exact resolve eq430 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq499 : ∀ X0 : G, y = (M.op (M.op (M.op X0 (M.op x y)) X0) x) := by
    intro X0
    first
    | (have i₁ := eq430 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq430
    | (have j0 := eq430 X0 x y
       grind)
    | exact resolve eq430 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X0 X2)) (M.op y (M.op x y))) = (M.op (M.op (M.op X1 X0) X1) x) := by
    intro X0 X1 X2
    first
    | exact superpose eq79 eq430
    | exact resolve eq430 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq504 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq430
    | (have j0 := eq430 X0 (σ x) (σ y)
       grind)
    | exact resolve eq430 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op x X0) (M.op y (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq76 eq430
    | exact resolve eq430 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq516 : (M.op y (M.op x y)) = (M.op (M.op x x) (M.op y (M.op x y))) := by
    first
    | exact superpose eq77 eq430
    | exact resolve eq430 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq530 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op X1 X0) (M.op y (M.op x y)))) = (M.op (M.op X2 (M.op X1 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq79 X1 (M.op (M.op X2 (M.op X1 X0)) X2)
       have i₂ := eq430 X2 X1 X0
       grind)
    | exact superpose eq430 eq79
    | exact resolve eq79 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq541 : ∀ X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X3 (M.op (M.op X4 (M.op X2 X4)) X3))) = (M.op (M.op X5 (M.op x (M.op (M.op X1 X2) (M.op y (M.op x y))))) X5) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq400 x X1 X2 X3 X4 X5
       have i₂ := eq530 X2 X1 x
       grind)
    | exact superpose eq530 eq400
    | exact resolve eq400 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq543 : ∀ X1 X2 X3 : G, (M.op x (M.op (M.op (M.op X3 (M.op X2 X3)) (M.op x (M.op (M.op X1 X2) (M.op y (M.op x y))))) (M.op y (M.op x y)))) = X1 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq431 x X1 X2 X3
       have i₂ := eq530 X2 X1 x
       grind)
    | exact superpose eq530 eq431
    | exact resolve eq431 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq552 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 x)) (M.op X2 (M.op X1 X2))) = (M.op x (M.op (M.op X0 (M.op y (M.op x y))) (M.op y (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq402 X1 X1 X2 X2
       have i₂ := eq530 (M.op y sF0) X1 X2
       grind)
    | exact superpose eq530 eq402
    | exact resolve eq402 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq580 : ∀ X1 X2 X3 X4 : G, (M.op X1 (M.op X3 (M.op (M.op X4 (M.op X2 X4)) X3))) = (M.op x (M.op (M.op x (M.op (M.op X1 X2) (M.op y (M.op x y)))) (M.op y (M.op x y)))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq541 X1 X2 X3 X4 X2
       have i₂ := eq530 (M.op (M.op X1 X2) (M.op y sF0)) x X2
       grind)
    | exact superpose eq530 eq541
    | exact resolve eq541 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq586 : ∀ X1 X2 X3 X4 : G, (M.op X1 (M.op X3 (M.op (M.op X4 (M.op X2 X4)) X3))) = (M.op x (M.op (M.op X1 X2) x)) := by
    intro X1 X2 X3 X4
    first
    | exact superpose eq337 eq580
    | exact resolve eq580 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337 eq580
  have eq590 : ∀ X2 : G, (M.op (M.op X2 x) X2) = (M.op x (M.op (M.op y (M.op x y)) x)) := by
    intro X2
    first
    | (have i₁ := eq467 x x X2
       have i₂ := eq586 y sF0 x x
       grind)
    | exact superpose eq586 eq467
    | exact resolve eq467 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq597 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X0) = (M.op x (M.op (M.op (σ x) (σ y)) (M.op y (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq504 eq79
    | exact resolve eq79 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq598 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X0) = (M.op x (M.op (M.op (σ x) (σ y)) (M.op y (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq26 eq597
    | (have j0 := eq597 X0
       grind)
    | exact resolve eq597 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq601 : ∀ X0 : G, (M.op (σ x) (M.op X0 (M.op (σ y) X0))) = (M.op x (M.op (M.op (σ x) (σ y)) (M.op y (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq598 eq410
    | exact resolve eq410 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq598
  have eq629 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op (M.op y (M.op x y)) y)) = X0 := by
    intro X0
    first
    | exact superpose eq473 eq436
    | exact resolve eq436 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq630 : ∀ X0 : G, x = (M.op (M.op X0 (M.op (M.op x y) X0)) (M.op (M.op y (M.op x y)) (M.op (M.op y (M.op x y)) y))) := by
    intro X0
    first
    | exact superpose eq473 eq76
    | exact resolve eq76 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq678 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op (M.op (M.op y (M.op x y)) y) X0)) := by
    intro X0
    first
    | exact superpose eq629 eq436
    | exact resolve eq436 eq629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq972 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op y (M.op x y)) (M.op X0 (M.op (M.op (M.op y (M.op x y)) y) X0))) x) := by
    intro X0
    first
    | exact superpose eq76 eq678
    | exact resolve eq678 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq973 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op (M.op X1 (M.op X0 X1)) (M.op X2 (M.op (M.op (M.op y (M.op x y)) y) X2))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq678 (M.op (M.op X1 (M.op X2 X1)) (M.op x (M.op (M.op (M.op y sF0) y) x)))
       have i₂ := eq54 (M.op (M.op y sF0) y) X1 X2 x
       grind)
    | exact superpose eq54 eq678
    | exact resolve eq678 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1007 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op X1 (M.op X0 X1)) (M.op x y)) X0) := by
    intro X0 X1
    first
    | exact superpose eq678 eq973
    | exact resolve eq973 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973
  have eq1008 : (M.op x y) = (M.op (M.op (M.op y (M.op x y)) (M.op x y)) x) := by
    first
    | exact superpose eq678 eq972
    | exact resolve eq972 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678 eq972
  have eq1022 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x (M.op x y))) := by
    first
    | exact superpose eq1008 eq436
    | exact resolve eq436 eq1008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1037 : (M.op (M.op y (M.op x y)) (M.op (M.op y (M.op x y)) y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq1022 eq629
    | exact resolve eq629 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq1051 : ∀ X0 : G, x = (M.op (M.op X0 (M.op (M.op x y) X0)) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1037 eq630
    | exact resolve eq630 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630 eq1037
  have eq1065 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op (M.op x (M.op x y)) x)) = X0 := by
    intro X0
    first
    | exact superpose eq1051 eq436
    | exact resolve eq436 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1067 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op x y) X0)) (M.op (M.op X1 (M.op X2 X1)) (M.op (M.op x (M.op x y)) x))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq1051 eq54
    | exact resolve eq54 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051
  have eq1199 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op x y)) X1)) = (M.op X0 (M.op (M.op x (M.op x y)) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq1065 (M.op X1 (M.op (M.op x sF0) X1))
       have i₂ := eq436 sF0 X1 x
       grind)
    | exact superpose eq436 eq1065
    | exact resolve eq1065 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1207 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op (M.op (M.op x (M.op x y)) x) X0)) := by
    intro X0
    first
    | exact superpose eq1065 eq436
    | exact resolve eq436 eq1065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1218 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op X1 (M.op X0 X1)) (M.op y (M.op (M.op x (M.op x y)) x))) := by
    intro X0 X1
    first
    | exact superpose eq1199 eq422
    | exact resolve eq422 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq1221 : ∀ X2 : G, (M.op (M.op X2 x) X2) = (M.op y (M.op (M.op x (M.op x y)) x)) := by
    intro X2
    first
    | exact superpose eq1199 eq590
    | exact resolve eq590 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590 eq1199
  have eq1246 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op (M.op x (M.op x y)) x) X0) (M.op x y)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq1065 eq1007
    | exact resolve eq1007 eq1065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1257 : (M.op x y) = (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op x y)) (σ x)) := by
    first
    | exact superpose eq26 eq1007
    | (have j0 := eq1007 (σ x) (σ y)
       grind)
    | exact resolve eq1007 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1271 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op x y) (M.op X0 (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq1007 eq436
    | exact resolve eq436 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq1288 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op (σ x) (M.op x y))) := by
    first
    | exact superpose eq1257 eq436
    | exact resolve eq436 eq1257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257
  have eq1370 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (M.op (M.op x y) (M.op (σ x) (M.op x y))) X0))) := by
    intro X0
    first
    | exact superpose eq1288 eq436
    | exact resolve eq436 eq1288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1442 : ∀ X0 : G, (M.op (M.op (M.op (M.op x (M.op x y)) x) X0) (M.op x y)) = (M.op (M.op x y) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1207 eq1271
    | exact resolve eq1271 eq1207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207
  have eq1452 : (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) = (M.op (M.op x y) (M.op (M.op x x) (M.op x y))) := by
    first
    | exact superpose eq516 eq1271
    | exact resolve eq1271 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq1476 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1271 X0 X1
       have i₂ := eq1271 X0 sF0
       grind)
    | exact superpose eq1271 eq1271
    | exact resolve eq1271 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1519 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1022
       have i₂ := eq1271 x sF0
       grind)
    | exact superpose eq1271 eq1022
    | exact resolve eq1022 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq1527 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op x (M.op x y)) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq1065 (M.op X0 sF0)
       have i₂ := eq1271 X0 sF0
       grind)
    | exact superpose eq1271 eq1065
    | exact resolve eq1065 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065
  have eq1554 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op (M.op x y) X0)) (M.op X2 (M.op x y))) = X2 := by
    intro X0 X2
    first
    | exact superpose eq1527 eq1067
    | exact resolve eq1067 eq1527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067 eq1527
  have eq1585 : ∀ X0 X1 : G, (M.op (M.op X1 x) X1) = (M.op x (M.op X0 (M.op (M.op (M.op x y) (M.op (M.op x x) (M.op x y))) X0))) := by
    intro X0 X1
    first
    | exact superpose eq1452 eq407
    | exact resolve eq407 eq1452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407 eq1452
  have eq1619 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op X0 (M.op x y))) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq1442 eq1246
    | exact resolve eq1246 eq1442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246 eq1442
  have eq1671 : ∀ X1 : G, (M.op (M.op X1 x) X1) = (M.op x (M.op (M.op x (M.op x x)) x)) := by
    intro X1
    first
    | (have i₁ := eq1585 x X1
       have i₂ := eq586 x (M.op x x) x sF0
       grind)
    | exact superpose eq586 eq1585
    | exact resolve eq1585 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586 eq1585
  have eq1700 : ∀ X1 : G, (M.op (M.op X1 x) X1) = (M.op x (M.op x (M.op (M.op x x) (M.op y (M.op x y))))) := by
    intro X1
    first
    | (have i₁ := eq1671 X1
       have i₂ := eq530 x x x
       grind)
    | exact superpose eq530 eq1671
    | exact resolve eq1671 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq1671
  have eq1702 : ∀ X1 : G, (M.op (M.op X1 x) X1) = (M.op x (M.op x (M.op y (M.op x y)))) := by
    intro X1
    first
    | exact superpose eq328 eq1700
    | exact resolve eq1700 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1700
  have eq1709 : (M.op y (M.op (M.op x (M.op x y)) x)) = (M.op x (M.op x (M.op y (M.op x y)))) := by
    first
    | (have i₁ := eq1221 x
       have i₂ := eq1702 x
       grind)
    | exact superpose eq1702 eq1221
    | exact resolve eq1221 eq1702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221
  have eq1714 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op X1 (M.op X0 X1)) (M.op x (M.op x (M.op y (M.op x y))))) := by
    intro X0 X1
    first
    | exact superpose eq1709 eq1218
    | exact resolve eq1218 eq1709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218 eq1709
  have eq1737 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) (σ (τ X1))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ (τ X1))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X1 X0
       have i₂ := eq373 X0 (τ X1)
       grind)
    | exact superpose eq373 eq49
    | (have j1 := eq373 X0 (τ X1)
       grind)
    | exact resolve eq49 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq1748 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ (τ X1))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1737 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1737
    | (have j0 := eq1737 X0 X1
       grind)
    | exact resolve eq1737 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1737
  have eq1752 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1748 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq1748 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq1748 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1748
  have eq1756 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1752 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1752
    | (have j0 := eq1752 X0 X1
       grind)
    | exact resolve eq1752 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1752
  have eq1778 : ∀ X0 X1 : G, (M.op X1 (M.op y X1)) = (M.op (M.op x y) (M.op X0 (M.op x X0))) := by
    intro X0 X1
    first
    | exact superpose eq1519 eq1271
    | exact resolve eq1271 eq1519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1801 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x (M.op X1 X0)) (M.op y (M.op x y)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq436 X0 (M.op x (M.op X1 X0)) X1
       have i₂ := eq1519 (M.op X1 X0)
       grind)
    | exact superpose eq1519 eq436
    | exact resolve eq436 eq1519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1847 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X1) (M.op (M.op X0 (M.op x y)) X0)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1554 eq436
    | exact resolve eq436 eq1554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554
  have eq1888 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) (M.op x y)) = (M.op X1 (M.op X0 (M.op X2 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1847 eq54
    | exact resolve eq54 eq1847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1889 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op x y)) = (M.op x (M.op X0 (M.op y (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq1847 eq79
    | exact resolve eq79 eq1847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1898 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (M.op (M.op x y) X0) (M.op x y))) = (M.op (M.op (M.op X1 (M.op x y)) X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq1847 eq1271
    | exact resolve eq1271 eq1847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1847
  have eq1900 : y = (M.op (M.op x y) (M.op (M.op (M.op x y) x) (M.op x y))) := by
    first
    | exact superpose eq1898 eq499
    | exact resolve eq499 eq1898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499 eq1898
  have eq1906 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X1 X2)))) = (M.op x (M.op X0 (M.op y (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1889 eq1888
    | exact resolve eq1888 eq1889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1888
  have eq1914 : y = (M.op (M.op x y) (M.op x (M.op x (M.op y (M.op x y))))) := by
    first
    | (have i₁ := eq1900
       have i₂ := eq1702 sF0
       grind)
    | exact superpose eq1702 eq1900
    | exact resolve eq1900 eq1702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1900
  have eq1938 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1619 X0
       have i₂ := eq1271 X0 sF0
       grind)
    | exact superpose eq1271 eq1619
    | exact resolve eq1619 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1939 : (M.op x y) = (M.op (M.op y (M.op x y)) (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq1619 x
       have i₂ := eq1519 sF0
       grind)
    | exact superpose eq1519 eq1619
    | exact resolve eq1619 eq1519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1619
  have eq1983 : ∀ X0 X1 : G, (M.op (M.op y (M.op x y)) (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op (M.op x y) x) (M.op x y)))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1939 eq54
    | exact resolve eq54 eq1939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1939
  have eq1993 : ∀ X0 X1 : G, (M.op (M.op y (M.op x y)) (M.op (M.op X0 (M.op X1 X0)) (M.op x (M.op x (M.op y (M.op x y)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1983 X0 X1
       have i₂ := eq1702 sF0
       grind)
    | exact superpose eq1702 eq1983
    | exact resolve eq1983 eq1702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1702 eq1983
  have eq2000 : ∀ X1 : G, (M.op (M.op y (M.op x y)) (M.op X1 x)) = X1 := by
    intro X1
    first
    | exact superpose eq1714 eq1993
    | exact resolve eq1993 eq1714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1714 eq1993
  have eq2302 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X2 (M.op x y))) = (M.op (M.op X1 X2) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1271 X2 (M.op X1 X2)
       have i₂ := eq1476 X2 X1 X0
       grind)
    | (have i₁ := eq1271 X2 (M.op X1 X2)
       have i₂ := eq1476 X0 X1 X2
       grind)
    | exact superpose eq1476 eq1271
    | exact resolve eq1271 eq1476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2328 : ∀ X0 X2 X4 : G, (M.op (M.op X4 X0) X4) = (M.op (M.op x y) (M.op (M.op X2 (M.op X0 X2)) (M.op x y))) := by
    intro X0 X2 X4
    first
    | (have i₁ := eq401 X0 x X2 x X4
       have i₂ := eq2302 x x (M.op X2 (M.op X0 X2))
       grind)
    | exact superpose eq2302 eq401
    | exact resolve eq401 eq2302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq2329 : ∀ X0 : G, (M.op x (M.op (M.op X0 (M.op y (M.op x y))) (M.op y (M.op x y)))) = (M.op (M.op x y) (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq552 X0 x x
       have i₂ := eq2302 x x (M.op X0 x)
       grind)
    | exact superpose eq2302 eq552
    | exact resolve eq552 eq2302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552 eq2302
  have eq2531 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op x y) X0) (M.op x y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1938 eq436
    | exact resolve eq436 eq1938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2541 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X0)) = (M.op (M.op (M.op x y) X2) (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1938 eq1476
    | exact resolve eq1476 eq1938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1938
  have eq2542 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X0)) = (M.op x (M.op X2 (M.op y (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1889 eq2541
    | exact resolve eq2541 eq1889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2541
  have eq2550 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op x (M.op X0 (M.op y (M.op x y))))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1889 eq2531
    | exact resolve eq2531 eq1889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1889 eq2531
  have eq2587 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op x (M.op (σ x) (M.op y (M.op x y))))) := by
    first
    | (have i₁ := eq1370 x
       have i₂ := eq2542 x sF0 sF2
       grind)
    | exact superpose eq2542 eq1370
    | exact resolve eq1370 eq2542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370
  have eq2592 : ∀ X0 X4 : G, (M.op (M.op X4 X0) X4) = (M.op x (M.op X0 (M.op y (M.op x y)))) := by
    intro X0 X4
    first
    | (have i₁ := eq2328 x x X4
       have i₂ := eq2542 sF0 x x
       grind)
    | exact superpose eq2542 eq2328
    | exact resolve eq2328 eq2542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2328 eq2542
  have eq2600 : ∀ X0 X2 X3 : G, (M.op (M.op x (M.op X0 (M.op y (M.op x y)))) (M.op X2 (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq493 X0 x X2 X3
       have i₂ := eq2592 X0 x
       grind)
    | exact superpose eq2592 eq493
    | exact resolve eq493 eq2592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq2601 : ∀ X0 X2 : G, (M.op (M.op X2 (M.op X0 X2)) (M.op y (M.op x y))) = (M.op (M.op x (M.op X0 (M.op y (M.op x y)))) x) := by
    intro X0 X2
    first
    | (have i₁ := eq502 X0 x X2
       have i₂ := eq2592 X0 x
       grind)
    | exact superpose eq2592 eq502
    | exact resolve eq502 eq2592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq2660 : ∀ X0 X2 : G, (M.op (M.op X2 (M.op X0 X2)) (M.op y (M.op x y))) = (M.op x (M.op (M.op X0 (M.op y (M.op x y))) (M.op y (M.op x y)))) := by
    intro X0 X2
    first
    | (have i₁ := eq2601 X0 X2
       have i₂ := eq2592 (M.op X0 (M.op y sF0)) x
       grind)
    | exact superpose eq2592 eq2601
    | exact resolve eq2601 eq2592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2601
  have eq2663 : ∀ X0 X2 : G, (M.op (M.op X2 (M.op X0 X2)) (M.op y (M.op x y))) = (M.op (M.op x y) (M.op (M.op X0 x) (M.op x y))) := by
    intro X0 X2
    first
    | exact superpose eq2329 eq2660
    | exact resolve eq2660 eq2329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2329 eq2660
  have eq3596 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op x (M.op X0 (M.op y (M.op x y)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq436 X0 X1 X1
       have i₂ := eq2592 X0 X1
       grind)
    | exact superpose eq2592 eq436
    | exact resolve eq436 eq2592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq3604 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op x (M.op (M.op X1 (M.op x (M.op X0 (M.op y (M.op x y))))) (M.op y (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X1 (M.op X1 X0)
       have i₂ := eq2592 X0 X1
       grind)
    | exact superpose eq2592 eq79
    | exact resolve eq79 eq2592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq3608 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) X1)) = (M.op X2 (M.op x (M.op X0 (M.op y (M.op x y))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1476 X1 (M.op X2 X0) X2
       have i₂ := eq2592 X0 X2
       grind)
    | exact superpose eq2592 eq1476
    | exact resolve eq1476 eq2592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3641 : ∀ X0 X2 : G, (M.op (M.op X2 (M.op X0 X2)) (M.op y (M.op x y))) = (M.op X0 (M.op x (M.op x (M.op y (M.op x y))))) := by
    intro X0 X2
    first
    | (have i₁ := eq2663 X2 X2
       have i₂ := eq3608 x sF0 X2
       grind)
    | exact superpose eq3608 eq2663
    | exact resolve eq2663 eq3608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2663
  have eq3644 : ∀ X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X3)) (M.op X1 X2)) = X1 := by
    intro X1 X2 X3
    first
    | exact superpose eq3604 eq543
    | exact resolve eq543 eq3604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543 eq3604
  have eq3808 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) (M.op y (M.op x y))) (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3644 X1 X0 (M.op x X0)
       have i₂ := eq1519 X0
       grind)
    | (have i₁ := eq3644 X1 y (M.op x y)
       have i₂ := eq1519 X0
       grind)
    | exact superpose eq1519 eq3644
    | exact resolve eq3644 eq1519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3817 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 (M.op x X0))) (M.op X1 y)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1519 eq3644
    | exact resolve eq3644 eq1519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3836 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X1)) (M.op x (M.op X0 (M.op y (M.op x y))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3644 (M.op X2 X0) X2 X1
       have i₂ := eq2592 X0 X2
       grind)
    | exact superpose eq2592 eq3644
    | exact resolve eq3644 eq2592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4329 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (M.op X0 X2) (M.op (M.op x X0) (M.op y (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1476 X1 X2 (M.op X0 X2)
       have i₂ := eq508 X0 X2
       grind)
    | (have i₁ := eq1476 X0 (M.op x X0) (M.op y (M.op x y))
       have i₂ := eq508 X0 X1
       grind)
    | exact superpose eq508 eq1476
    | exact resolve eq1476 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4330 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X1) (M.op y (M.op x y)))) = (M.op (M.op (M.op x X0) (M.op y (M.op x y))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2592 (M.op X0 X1) X1
       have i₂ := eq508 X0 X1
       grind)
    | (have i₁ := eq2592 (M.op y (M.op x y)) (M.op x X0)
       have i₂ := eq508 X0 X1
       grind)
    | exact superpose eq508 eq2592
    | exact resolve eq2592 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4566 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X1 (M.op x (M.op X0 (M.op y X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3596 sF0 X1
       have i₂ := eq1271 y sF0
       grind)
    | exact superpose eq1271 eq3596
    | exact resolve eq3596 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5204 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op (M.op X0 x) (M.op (M.op x X0) (M.op y (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq2000 eq1801
    | exact resolve eq1801 eq2000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2000
  have eq5424 : ∀ X0 X1 : G, (M.op (M.op x (M.op X0 X1)) (M.op y (M.op x y))) = (M.op X0 (M.op x (M.op X1 (M.op y (M.op x y))))) := by
    intro X0 X1
    first
    | exact superpose eq1801 eq2550
    | exact resolve eq2550 eq1801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5463 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X1) (M.op x (M.op X0 (M.op y X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2550 sF0 X1
       have i₂ := eq1271 y sF0
       grind)
    | exact superpose eq1271 eq2550
    | exact resolve eq2550 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271
  have eq5464 : ∀ X0 X1 : G, (M.op (M.op (M.op x (M.op X0 x)) X1) X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1801 eq2550
    | exact resolve eq2550 eq1801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1801
  have eq5542 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X0)) X2) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5464 X1 X2
       have i₂ := eq1476 x X1 X0
       grind)
    | (have i₁ := eq5464 X1 X2
       have i₂ := eq1476 X0 X1 x
       grind)
    | exact superpose eq1476 eq5464
    | exact resolve eq5464 eq1476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5464
  have eq5719 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) (M.op X0 (M.op x X0))) X1) y) = X1 := by
    intro X0 X1
    first
    | exact superpose eq437 eq5542
    | exact resolve eq5542 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq5734 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) (M.op X0 (M.op x X0))) X2) = (M.op y (M.op X1 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5542 X1 X2 (M.op y (M.op X1 (M.op X2 X1)))
       have i₂ := eq1778 X0 (M.op X1 (M.op X2 X1))
       grind)
    | exact superpose eq1778 eq5542
    | exact resolve eq5542 eq1778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1778
  have eq5883 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X1) (M.op y (M.op x y)))) = (M.op X0 (M.op (M.op x X1) (M.op y (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq3808 eq2592
    | exact resolve eq2592 eq3808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6071 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X1 (M.op x X1))) = (M.op (M.op (M.op x (M.op X0 y)) (M.op y (M.op x y))) X0) := by
    intro X0 X1
    first
    | exact superpose eq3817 eq3808
    | exact resolve eq3808 eq3817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3817
  have eq6074 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X1 (M.op x X1))) = (M.op x (M.op (M.op (M.op X0 y) X0) (M.op y (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq4330 eq6071
    | exact resolve eq6071 eq4330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4330 eq6071
  have eq6093 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X1 (M.op x X1))) = (M.op (M.op X0 y) (M.op (M.op x X0) (M.op y (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq5883 eq6074
    | exact resolve eq6074 eq5883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5883 eq6074
  have eq11079 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op X3 X0) X2))) = (M.op X1 (M.op (M.op x (M.op X3 (M.op y (M.op x y)))) X0)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq2550 eq427
    | exact resolve eq427 eq2550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11443 : ∀ X0 X1 X3 : G, (M.op X1 (M.op X3 (M.op x (M.op X0 (M.op y (M.op x y)))))) = (M.op X1 (M.op (M.op x (M.op X3 (M.op y (M.op x y)))) X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq11079 X0 X1 x X3
       have i₂ := eq3608 X0 x X3
       grind)
    | exact superpose eq3608 eq11079
    | exact resolve eq11079 eq3608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11079
  have eq11645 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op (σ x) (M.op X0 (M.op (σ y) X0))))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq601 eq3596
    | exact resolve eq3596 eq601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12104 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) X1) (M.op X0 (M.op y (M.op x y)))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq328 eq2550
    | exact resolve eq2550 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq12281 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 x) X0) = (M.op X1 (M.op (M.op (M.op X2 (M.op y (M.op x y))) X0) (M.op X3 (M.op X1 X3)))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq12104 eq54
    | exact resolve eq54 eq12104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14560 : ∀ X0 X1 X3 X4 : G, (M.op X1 (M.op (M.op x X0) (M.op y (M.op x y)))) = (M.op X3 (M.op (M.op X1 X0) (M.op X4 (M.op X3 X4)))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq415 X3 X1 x X0 X4
       have i₂ := eq508 X0 x
       grind)
    | (have i₁ := eq415 X0 X1 (M.op x y) y X4
       have i₂ := eq508 y X1
       grind)
    | exact superpose eq508 eq415
    | exact resolve eq415 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14807 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op x (M.op (M.op X0 X2) (M.op X3 (M.op X4 X3)))) (M.op y (M.op x y))) (M.op X0 (M.op X1 (M.op X2 X1)))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3808 (M.op (M.op X0 X2) (M.op X3 (M.op X4 X3))) X4
       have i₂ := eq415 X4 X0 X1 X2 X3
       grind)
    | (have i₁ := eq3808 (M.op X2 (M.op X3 X2)) X1
       have i₂ := eq415 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq415 eq3808
    | exact resolve eq3808 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq14862 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X2) (M.op x (M.op (M.op X3 (M.op X4 X3)) (M.op y (M.op x y))))) (M.op X0 (M.op X1 (M.op X2 X1)))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq5424 eq14807
    | exact resolve eq14807 eq5424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14807
  have eq15029 : ∀ X0 X2 : G, (M.op (M.op X2 x) X0) = (M.op (M.op X2 (M.op y (M.op x y))) (M.op (M.op x X0) (M.op y (M.op x y)))) := by
    intro X0 X2
    first
    | (have i₁ := eq12281 X0 x X2 x
       have i₂ := eq14560 X0 (M.op X2 (M.op y sF0)) x x
       grind)
    | exact superpose eq14560 eq12281
    | exact resolve eq12281 eq14560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12281 eq14560
  have eq15072 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op X0 X2) (M.op x (M.op X4 (M.op x (M.op x (M.op y (M.op x y))))))) (M.op X0 (M.op X1 (M.op X2 X1)))) = X4 := by
    intro X0 X1 X2 X4
    first
    | exact superpose eq3641 eq14862
    | exact resolve eq14862 eq3641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3641 eq14862
  have eq15176 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op X0 X2) X4) (M.op X0 (M.op X1 (M.op X2 X1)))) = X4 := by
    intro X0 X1 X2 X4
    first
    | exact superpose eq3596 eq15072
    | exact resolve eq15072 eq3596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15072
  have eq15383 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op x y) (M.op X4 (M.op x X4))) X0) = (M.op (M.op X1 (M.op X2 (M.op X3 X2))) (M.op (M.op y X0) (M.op X1 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq5719 eq444
    | exact resolve eq444 eq5719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5719
  have eq15526 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X1 (M.op X0 X1)) (M.op X2 X3)) X0) (M.op X5 (M.op X2 (M.op X4 (M.op X3 X4))))) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq3644 X5 (M.op X2 (M.op X4 (M.op X3 X4))) (M.op (M.op X1 (M.op X0 X1)) (M.op X2 X3))
       have i₂ := eq444 X2 X4 X3 X1 X0
       grind)
    | exact superpose eq444 eq3644
    | exact resolve eq3644 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15531 : ∀ X2 X3 X4 X5 : G, (M.op (M.op X2 X3) (M.op X5 (M.op X2 (M.op X4 (M.op X3 X4))))) = X5 := by
    intro X2 X3 X4 X5
    first
    | (have i₁ := eq15526 x x X2 X3 X4 X5
       have i₂ := eq5542 x x (M.op X2 X3)
       grind)
    | exact superpose eq5542 eq15526
    | exact resolve eq15526 eq5542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15526
  have eq16957 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X4 (M.op X1 (M.op X5 (M.op (M.op (M.op X2 (M.op X0 X2)) (M.op X3 (M.op X1 X3))) X5))))) = X4 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq15531 X1 (M.op (M.op X2 (M.op X0 X2)) (M.op X3 (M.op X1 X3))) X5 X4
       have i₂ := eq54 X1 X2 X0 X3
       grind)
    | exact superpose eq54 eq15531
    | exact resolve eq15531 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq17032 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 (M.op X3 X2)) X0)) (M.op X4 (M.op X1 (M.op X3 X0)))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq15531 X1 (M.op (M.op X2 (M.op X3 X2)) X0) X3 X4
       have i₂ := eq5542 X2 X3 X0
       grind)
    | exact superpose eq5542 eq15531
    | exact resolve eq15531 eq5542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5542
  have eq17344 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 (M.op X1 (M.op (M.op X2 (M.op X0 X2)) (M.op x (M.op (M.op X3 (M.op X1 X3)) (M.op y (M.op x y)))))))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16957 X0 X1 X2 X3 X4 x
       have i₂ := eq3608 (M.op X3 (M.op X1 X3)) x (M.op X2 (M.op X0 X2))
       grind)
    | exact superpose eq3608 eq16957
    | exact resolve eq16957 eq3608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16957
  have eq17434 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X4 (M.op X1 (M.op X0 (M.op X3 (M.op X1 X3)))))) = X4 := by
    intro X0 X1 X3 X4
    first
    | exact superpose eq3836 eq17344
    | exact resolve eq17344 eq3836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17344
  have eq17810 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op x y) X1) (M.op x (M.op (M.op X0 (M.op X2 (M.op y (M.op X3 (M.op X2 X3))))) X0))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5463 (M.op X0 (M.op X2 (M.op y (M.op X3 (M.op X2 X3))))) X1
       have i₂ := eq17434 y X2 X3 X0
       grind)
    | exact superpose eq17434 eq5463
    | exact resolve eq5463 eq17434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5463
  have eq17835 : ∀ X1 X2 X3 : G, (M.op (M.op (M.op x y) X1) (M.op x (M.op x (M.op (M.op X2 (M.op y (M.op X3 (M.op X2 X3)))) (M.op y (M.op x y)))))) = X1 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq17810 x X1 X2 X3
       have i₂ := eq2592 (M.op X2 (M.op y (M.op X3 (M.op X2 X3)))) x
       grind)
    | exact superpose eq2592 eq17810
    | exact resolve eq17810 eq2592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17810
  have eq17941 : ∀ X1 X2 X3 : G, (M.op (M.op (M.op x y) X1) (M.op (M.op x (M.op x (M.op y (M.op x y)))) (M.op X2 (M.op y (M.op X3 (M.op X2 X3)))))) = X1 := by
    intro X1 X2 X3
    first
    | exact superpose eq11443 eq17835
    | exact resolve eq17835 eq11443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17835
  have eq19454 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X4) (M.op X1 (M.op X5 (M.op (M.op X0 (M.op X2 (M.op X1 (M.op X3 (M.op X2 X3))))) X5)))) = X4 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq15176 X1 X5 (M.op X0 (M.op X2 (M.op X1 (M.op X3 (M.op X2 X3))))) X4
       have i₂ := eq17434 X1 X2 X3 X0
       grind)
    | exact superpose eq17434 eq15176
    | exact resolve eq15176 eq17434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19608 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X1 (M.op (M.op x X0) (M.op y (M.op x y))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15176 X1 x X0 X2
       have i₂ := eq508 X0 x
       grind)
    | (have i₁ := eq15176 X0 (M.op x y) y x
       have i₂ := eq508 y X1
       grind)
    | exact superpose eq508 eq15176
    | exact resolve eq15176 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq19731 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X2 (M.op (M.op (M.op X3 X4) X0) X2))) = (M.op X1 (M.op (M.op X3 (M.op X5 (M.op X4 X5))) X0)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq427 X1 X2 (M.op (M.op X3 X4) X0) (M.op X3 (M.op X5 (M.op X4 X5)))
       have i₂ := eq15176 X3 X5 X4 X0
       grind)
    | exact superpose eq15176 eq427
    | exact resolve eq427 eq15176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427 eq15176
  have eq19765 : ∀ X0 X1 X3 X4 X5 : G, (M.op X1 (M.op (M.op X3 (M.op X5 (M.op X4 X5))) X0)) = (M.op X1 (M.op (M.op X3 X4) (M.op x (M.op X0 (M.op y (M.op x y)))))) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq19731 X0 X1 x X3 X4 X5
       have i₂ := eq3608 X0 x (M.op X3 X4)
       grind)
    | exact superpose eq3608 eq19731
    | exact resolve eq19731 eq3608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19731
  have eq19958 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X4) (M.op X1 (M.op X0 (M.op x (M.op (M.op X2 (M.op X1 (M.op X3 (M.op X2 X3)))) (M.op y (M.op x y))))))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq19454 X0 X1 X2 X3 X4 x
       have i₂ := eq3608 (M.op X2 (M.op X1 (M.op X3 (M.op X2 X3)))) x X0
       grind)
    | exact superpose eq3608 eq19454
    | exact resolve eq19454 eq3608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3608 eq19454
  have eq20048 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X4) (M.op X1 (M.op X0 (M.op X2 (M.op X1 X2))))) = X4 := by
    intro X0 X1 X2 X4
    first
    | exact superpose eq441 eq19958
    | exact resolve eq19958 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441 eq19958
  have eq20415 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1756 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1756
    | exact resolve eq1756 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20446 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq1756 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1756
    | (have j0 := eq1756 x X0
       grind)
    | exact resolve eq1756 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1756
  have eq20781 : (σ (k (M.op x y) x)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq33
       have i₂ := eq20415 sF2 sF1
       grind)
    | exact superpose eq20415 eq33
    | (have j1 := eq20415 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq33 eq20415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq20782 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq58
       have i₂ := eq20415 sF2 sF3
       grind)
    | exact superpose eq20415 eq58
    | (have j1 := eq20415 (σ x) (σ y)
       grind)
    | exact resolve eq58 eq20415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq20788 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq20782
    | exact resolve eq20782 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20782
  have eq20790 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq20788
    | exact resolve eq20788 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20788
  have eq20792 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20790
       have i₂ := eq20415 x y
       grind)
    | exact superpose eq20415 eq20790
    | (have j1 := eq20415 (σ x) (σ y)
       grind)
    | exact resolve eq20790 eq20415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20415 eq20790
  have eq20815 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20792
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20792
    | exact resolve eq20792 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20792
  have eq20819 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq20815
    | exact resolve eq20815 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20815
  have eq20821 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq20819
       have r₂ := eq27
       grind)
    | exact resolve eq20819 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20819
  have eq20823 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20821
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20821
    | exact resolve eq20821 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20821
  have eq20843 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op x (M.op (σ x) (M.op y (M.op x y))))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20823 eq2550
    | exact resolve eq2550 eq20823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20823
  have eq20859 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2587 eq20843
    | exact resolve eq20843 eq2587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20843
  have eq20902 : x = (M.op (M.op x y) (M.op x (M.op x (M.op y (M.op x y))))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2550 x x
       have i₂ := eq20859
       grind)
    | exact superpose eq20859 eq2550
    | exact resolve eq2550 eq20859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20859
  have eq20918 : (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1914 eq20902
    | exact resolve eq20902 eq1914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1914 eq20902
  have eq20935 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq20918 eq39
    | exact resolve eq39 eq20918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq20918
  have eq20951 : x = y ∨ x = y := by
    first
    | exact superpose eq38 eq20935
    | exact resolve eq20935 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20935
  have eq20952 : x = y := by grind
  clear eq20951
  have eq20956 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq20952
       grind)
    | exact superpose eq20952 eq18
    | exact resolve eq18 eq20952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq20957 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq20952
       grind)
    | exact superpose eq20952 eq24
    | exact resolve eq24 eq20952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq20989 : ∀ X0 : G, (M.op (σ x) (M.op X0 (M.op (σ y) X0))) = (M.op x (M.op (M.op (σ x) (σ y)) (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq601 X0
       have i₂ := eq20952
       grind)
    | exact superpose eq20952 eq601
    | exact resolve eq601 eq20952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq20995 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1519 X0
       have i₂ := eq20952
       grind)
    | exact superpose eq20952 eq1519
    | exact resolve eq1519 eq20952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1519
  have eq21008 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X1 X2)))) = (M.op x (M.op X0 (M.op x (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1906 X0 X1 X2
       have i₂ := eq20952
       grind)
    | exact superpose eq20952 eq1906
    | exact resolve eq1906 eq20952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1906
  have eq21013 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op x (M.op X0 (M.op x (M.op x y))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2550 X0 X1
       have i₂ := eq20952
       grind)
    | exact superpose eq20952 eq2550
    | exact resolve eq2550 eq20952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2550
  have eq21014 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op x (M.op (σ x) (M.op x (M.op x y))))) := by
    first
    | (have i₁ := eq2587
       have i₂ := eq20952
       grind)
    | exact superpose eq20952 eq2587
    | exact resolve eq2587 eq20952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2587
  have eq21015 : ∀ X0 X4 : G, (M.op (M.op X4 X0) X4) = (M.op x (M.op X0 (M.op x (M.op x y)))) := by
    intro X0 X4
    first
    | (have i₁ := eq2592 X0 X4
       have i₂ := eq20952
       grind)
    | exact superpose eq20952 eq2592
    | exact resolve eq2592 eq20952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2592
  have eq21016 : ∀ X0 X2 X3 : G, (M.op (M.op x (M.op X0 (M.op x (M.op x y)))) (M.op X2 (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq2600 X0 X2 X3
       have i₂ := eq20952
       grind)
    | exact superpose eq20952 eq2600
    | exact resolve eq2600 eq20952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2600
  have eq21084 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op x (M.op X0 (M.op x (M.op x y)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3596 X0 X1
       have i₂ := eq20952
       grind)
    | exact superpose eq20952 eq3596
    | exact resolve eq3596 eq20952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3596
  have eq21099 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) (M.op x (M.op x y))) (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3808 X0 X1
       have i₂ := eq20952
       grind)
    | exact superpose eq20952 eq3808
    | exact resolve eq3808 eq20952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3808
  have eq21102 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X1)) (M.op x (M.op X0 (M.op x (M.op x y))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3836 X0 X1 X2
       have i₂ := eq20952
       grind)
    | exact superpose eq20952 eq3836
    | exact resolve eq3836 eq20952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3836
  have eq21112 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (M.op X0 X2) (M.op (M.op x X0) (M.op x (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4329 X0 X1 X2
       have i₂ := eq20952
       grind)
    | exact superpose eq20952 eq4329
    | exact resolve eq4329 eq20952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4329
  have eq21121 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X1 (M.op x (M.op X0 (M.op x X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4566 X0 X1
       have i₂ := eq20952
       grind)
    | exact superpose eq20952 eq4566
    | exact resolve eq4566 eq20952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4566
  have eq21137 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op X0 x) (M.op (M.op x X0) (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq5204 X0
       have i₂ := eq20952
       grind)
    | exact superpose eq20952 eq5204
    | exact resolve eq5204 eq20952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5204
  have eq21140 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op X1 (M.op x (M.op x y))))) = (M.op (M.op x (M.op X0 X1)) (M.op x (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq5424 X0 X1
       have i₂ := eq20952
       grind)
    | exact superpose eq20952 eq5424
    | exact resolve eq5424 eq20952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5424
  have eq21172 : ∀ X0 X1 X2 : G, (M.op x (M.op X1 (M.op X2 X1))) = (M.op (M.op (M.op x y) (M.op X0 (M.op x X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5734 X0 X1 X2
       have i₂ := eq20952
       grind)
    | exact superpose eq20952 eq5734
    | exact resolve eq5734 eq20952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5734
  have eq21182 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X1 (M.op x X1))) = (M.op (M.op X0 x) (M.op (M.op x X0) (M.op x (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6093 X0 X1
       have i₂ := eq20952
       grind)
    | exact superpose eq20952 eq6093
    | exact resolve eq6093 eq20952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6093
  have eq21519 : ∀ X0 X1 X3 : G, (M.op X1 (M.op X3 (M.op x (M.op X0 (M.op x (M.op x y)))))) = (M.op X1 (M.op (M.op x (M.op X3 (M.op x (M.op x y)))) X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq11443 X0 X1 X3
       have i₂ := eq20952
       grind)
    | exact superpose eq20952 eq11443
    | exact resolve eq11443 eq20952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11443
  have eq21530 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) X1) (M.op X0 (M.op x (M.op x y)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12104 X0 X1
       have i₂ := eq20952
       grind)
    | exact superpose eq20952 eq12104
    | exact resolve eq12104 eq20952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12104
  have eq21854 : ∀ X0 X2 : G, (M.op (M.op X2 x) X0) = (M.op (M.op X2 (M.op x (M.op x y))) (M.op (M.op x X0) (M.op x (M.op x y)))) := by
    intro X0 X2
    first
    | (have i₁ := eq15029 X0 X2
       have i₂ := eq20952
       grind)
    | exact superpose eq20952 eq15029
    | exact resolve eq15029 eq20952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15029
  have eq21876 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op x y) (M.op X4 (M.op x X4))) X0) = (M.op (M.op X1 (M.op X2 (M.op X3 X2))) (M.op (M.op x X0) (M.op X1 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq15383 X0 X1 X2 X3 X4
       have i₂ := eq20952
       grind)
    | exact superpose eq20952 eq15383
    | exact resolve eq15383 eq20952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15383
  have eq22005 : ∀ X1 X2 X3 : G, (M.op (M.op (M.op x y) X1) (M.op (M.op x (M.op x (M.op x (M.op x y)))) (M.op X2 (M.op x (M.op X3 (M.op X2 X3)))))) = X1 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq17941 X1 X2 X3
       have i₂ := eq20952
       grind)
    | exact superpose eq20952 eq17941
    | exact resolve eq17941 eq20952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17941
  have eq22084 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X1 (M.op (M.op x X0) (M.op x (M.op x y))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19608 X0 X1 X2
       have i₂ := eq20952
       grind)
    | exact superpose eq20952 eq19608
    | exact resolve eq19608 eq20952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19608
  have eq22087 : ∀ X0 X1 X3 X4 X5 : G, (M.op X1 (M.op (M.op X3 (M.op X5 (M.op X4 X5))) X0)) = (M.op X1 (M.op (M.op X3 X4) (M.op x (M.op X0 (M.op x (M.op x y)))))) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq19765 X0 X1 X3 X4 X5
       have i₂ := eq20952
       grind)
    | exact superpose eq20952 eq19765
    | exact resolve eq19765 eq20952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19765 eq20952
  have eq22217 : ∀ X1 : G, (M.op (M.op (M.op x y) X1) (M.op x (M.op x (M.op x y)))) = X1 := by
    intro X1
    first
    | (have i₁ := eq22005 X1 X1 x
       have i₂ := eq20048 x X1 x (M.op x (M.op x sF0))
       grind)
    | (have i₁ := eq22005 X1 x x
       have i₂ := eq20048 x X1 x (M.op (M.op x (M.op x (M.op x sF0))) (M.op x (M.op x (M.op x (M.op x x)))))
       grind)
    | exact superpose eq20048 eq22005
    | exact resolve eq22005 eq20048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20048 eq22005
  have eq22267 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op (M.op x y) (M.op X1 (M.op x X1))) := by
    intro X1
    first
    | exact superpose eq21137 eq21182
    | exact resolve eq21182 eq21137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21137 eq21182
  have eq22291 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq20957
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20957
    | exact resolve eq20957 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20957
  have eq22334 : ∀ X1 X2 : G, (M.op x (M.op X1 (M.op X2 X1))) = (M.op (M.op x (M.op x y)) X2) := by
    intro X1 X2
    first
    | exact superpose eq22267 eq21172
    | exact resolve eq21172 eq22267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21172
  have eq22350 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x (M.op x y)) X0) = (M.op (M.op X1 (M.op X2 (M.op X3 X2))) (M.op (M.op x X0) (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq22267 eq21876
    | exact resolve eq21876 eq22267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21876 eq22267
  have eq22376 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq22291 eq26
    | exact resolve eq26 eq22291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq22377 : (M.op (M.op x y) (M.op (σ x) (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq22291 eq1288
    | exact resolve eq1288 eq22291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288
  have eq22388 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op (σ x) (M.op X0 (M.op (σ x) X0))))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq22291 eq11645
    | exact resolve eq11645 eq22291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11645
  have eq22419 : ∀ X0 : G, (M.op (σ x) (M.op X0 (M.op (σ x) X0))) = (M.op x (M.op (M.op (σ x) (σ y)) (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq22291 eq20989
    | exact resolve eq20989 eq22291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20989
  have eq22424 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op x (M.op (σ x) (M.op x (M.op x y))))) := by
    first
    | exact superpose eq22291 eq21014
    | exact resolve eq21014 eq22291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21014 eq22291
  have eq22907 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq22376 eq20446
    | (have j0 := eq20446 X0
       grind)
    | exact resolve eq20446 eq22376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20446
  have eq22911 : (σ (k (M.op x y) x)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq22376 eq20781
    | exact resolve eq20781 eq22376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20781
  have eq22955 : ∀ X0 : G, (M.op x y) ≠ (M.op x X0) ∨ x = (M.op x y) ∨ x = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq20956
       grind)
    | exact superpose eq20956 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq20956
       grind)
    | exact resolve eq13 eq20956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22956 : ∀ X0 : G, x ≠ (M.op x y) ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq20956
       grind)
    | exact superpose eq20956 eq12
    | (have j0 := eq12 X0 x
       grind)
    | exact resolve eq12 eq20956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22966 : ∀ X0 X1 X2 : G, x = (M.op (M.op X0 (M.op X1 (M.op X2 X1))) (M.op (M.op x (M.op x y)) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq444 X0 X1 X2 x x
       have i₂ := eq20956
       grind)
    | exact superpose eq20956 eq444
    | exact resolve eq444 eq20956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq22981 : x = (M.op (M.op x (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq22966 x x x
       have i₂ := eq22350 sF0 x x x
       grind)
    | exact superpose eq22350 eq22966
    | exact resolve eq22966 eq22350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22350 eq22966
  have eq22988 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq22376 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | exact resolve eq12 eq22376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23847 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op x y) X0)) (M.op X2 (M.op X1 (M.op (M.op x (M.op x (M.op x y))) X0)))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq22217 eq15531
    | exact resolve eq15531 eq22217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15531 eq22217
  have eq23969 : ∀ X0 : G, (k (τ X0) (τ (σ x))) = (τ (M.op (σ x) X0)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq22907 eq136
    | (have j1 := eq22907 X0
       grind)
    | exact resolve eq136 eq22907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22907
  have eq23977 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op (σ x) X0)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq38 eq23969
    | (have j0 := eq23969 X0
       grind)
    | exact resolve eq23969 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23969
  have eq24008 : ∀ X0 X1 : G, (M.op x y) ≠ (M.op X0 (M.op X1 X0)) ∨ x = (M.op x y) ∨ x = (k (M.op X1 x) x) := by
    intro X0 X1
    first
    | (have i₁ := eq22955 (M.op X1 x)
       have i₂ := eq1476 x X1 X0
       grind)
    | (have i₁ := eq22955 (M.op X1 x)
       have i₂ := eq1476 X0 X1 x
       grind)
    | exact superpose eq1476 eq22955
    | (have j0 := eq22955 (M.op X1 x)
       grind)
    | exact resolve eq22955 eq1476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22955
  have eq27790 : ∀ X0 X1 : G, (M.op (M.op x (M.op x y)) (M.op (M.op X1 x) X0)) = (M.op x (M.op (M.op X1 (M.op x (M.op x y))) X0)) := by
    intro X0 X1
    first
    | exact superpose eq21530 eq22334
    | exact resolve eq22334 eq21530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21530
  have eq29649 : ∀ X0 : G, (τ X0) = (k (τ (M.op X0 (M.op x (M.op (σ x) (M.op x (M.op x y)))))) x) ∨ (M.op (σ x) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq21084 eq23977
    | exact resolve eq23977 eq21084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23977
  have eq41668 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op (M.op x (M.op X3 (M.op x (M.op x y)))) (M.op X1 (M.op (M.op X0 (M.op X4 (M.op X3 X4))) X0))))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq21016 eq17434
    | exact resolve eq17434 eq21016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21016
  have eq41693 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x (M.op X3 (M.op x (M.op x y)))) (M.op X1 (M.op (M.op X0 X3) (M.op x (M.op X0 (M.op x (M.op x y))))))))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq41668 X0 X1 X2 X3 x
       have i₂ := eq22087 X0 X1 X0 X3 x
       grind)
    | exact superpose eq22087 eq41668
    | exact resolve eq41668 eq22087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22087 eq41668
  have eq41855 : ∀ X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x (M.op X3 (M.op x (M.op x y)))) (M.op X1 X3)))) = X2 := by
    intro X1 X2 X3
    first
    | exact superpose eq21013 eq41693
    | exact resolve eq41693 eq21013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41693
  have eq50311 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op (τ (σ x)) X0)) ∨ (M.op (τ (σ x)) (τ (σ x))) = (M.op (τ (σ x)) X0) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) := by
    intro X0
    first
    | (have i₁ := eq30 x
       have i₂ := eq377 sF2 x
       grind)
    | exact superpose eq377 eq30
    | (have j1 := eq377 (σ x) X0
       grind)
    | exact resolve eq30 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq377
  have eq50364 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op x X0)) ∨ (M.op (τ (σ x)) (τ (σ x))) = (M.op (τ (σ x)) X0) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) := by
    intro X0
    first
    | exact superpose eq38 eq50311
    | (have j0 := eq50311 X0
       grind)
    | exact resolve eq50311 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50311
  have eq50423 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ (σ (k X0 x)) = (σ (M.op x X0)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) := by
    intro X0
    first
    | exact superpose eq38 eq50364
    | (have j0 := eq50364 X0
       grind)
    | exact resolve eq50364 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50364
  have eq50466 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ (σ (k X0 x)) = (σ (M.op x X0)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) := by
    intro X0
    first
    | (have i₁ := eq50423 X0
       have i₂ := eq20956
       grind)
    | exact superpose eq20956 eq50423
    | (have j0 := eq50423 X0
       grind)
    | exact resolve eq50423 eq20956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50423
  have eq50500 : ∀ X0 : G, x = (M.op x x) ∨ (M.op x y) = (M.op x X0) ∨ (σ (k X0 x)) = (σ (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq38 eq50466
    | (have j0 := eq50466 X0
       grind)
    | exact resolve eq50466 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50466
  have eq50519 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op x X0)) ∨ (M.op x y) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq50500 X0
       have i₂ := eq20956
       grind)
    | exact superpose eq20956 eq50500
    | (have j0 := eq50500 X0
       grind)
    | exact resolve eq50500 eq20956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50500
  have eq50778 : ∀ X0 : G, (k X0 x) = (τ (σ (M.op x X0))) ∨ (M.op x y) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 x)
       have i₂ := eq50519 X0
       grind)
    | exact superpose eq50519 eq10
    | (have j1 := eq50519 X0
       grind)
    | exact resolve eq10 eq50519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50519
  have eq50828 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (M.op x y) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq50778 X0
       have i₂ := eq10 (M.op x X0)
       grind)
    | exact superpose eq10 eq50778
    | (have j0 := eq50778 X0
       grind)
    | exact resolve eq50778 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50778
  have eq50840 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (M.op x y) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq50828 X0
       have j1 := eq22956 X0
       grind)
    | (have r₁ := eq50828 X0
       have r₂ := eq22956 X0
       grind)
    | exact resolve eq50828 eq22956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50828
  have eq50893 : ∀ X0 : G, (k (τ X0) (τ x)) = (τ (M.op x X0)) ∨ (M.op x y) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq136 X0 x
       have i₂ := eq50840 X0
       grind)
    | exact superpose eq50840 eq136
    | (have j1 := eq50840 X0
       grind)
    | exact resolve eq136 eq50840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50840
  have eq50924 : ∀ X0 : G, (τ X0) = (k (τ (M.op X0 (M.op x (M.op x (M.op x (M.op x y)))))) (τ x)) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq21084 eq50893
    | exact resolve eq50893 eq21084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50893
  have eq58166 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X4 (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X0 X2)))) (M.op X3 X1)))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq21008 eq41855
    | exact resolve eq41855 eq21008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41855
  have eq58177 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1
    first
    | exact superpose eq21008 eq22424
    | exact resolve eq22424 eq21008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21008
  have eq76347 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op (M.op (M.op x X1) (M.op x (M.op x y))) (M.op (M.op x (M.op X0 X1)) (M.op x (M.op x y))))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq21099 eq22084
    | exact resolve eq22084 eq21099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21099
  have eq76961 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op (M.op (M.op x X1) x) (M.op X0 X1))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq21854 eq76347
    | exact resolve eq76347 eq21854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21854 eq76347
  have eq77163 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op (M.op x (M.op X1 (M.op x (M.op x y)))) (M.op X0 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76961 X0 X1 X2
       have i₂ := eq21015 X1 x
       grind)
    | exact superpose eq21015 eq76961
    | exact resolve eq76961 eq21015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76961
  have eq159724 : ∀ X0 : G, (σ (τ X0)) = (k (M.op X0 (M.op x (M.op (σ x) (M.op x (M.op x y))))) (σ x)) ∨ (M.op (σ x) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq29649 eq49
    | (have j1 := eq29649 X0
       grind)
    | exact resolve eq49 eq29649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159749 : ∀ X0 : G, (σ (τ X0)) = (k (M.op X0 (M.op x (M.op (σ x) (M.op x (M.op x y))))) (σ x)) ∨ (M.op (σ x) (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq159724 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq159724
    | (have j0 := eq159724 X0
       grind)
    | exact resolve eq159724 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159724
  have eq159788 : ∀ X0 : G, (k (M.op X0 (M.op x (M.op (σ x) (M.op x (M.op x y))))) (σ x)) = X0 ∨ (M.op (σ x) (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq159749 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq159749
    | (have j0 := eq159749 X0
       grind)
    | exact resolve eq159749 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159749
  have eq162827 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k (M.op X0 (σ x)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq21102 eq159788
    | (have j0 := eq159788 (M.op X1 (M.op X0 X1))
       grind)
    | exact resolve eq159788 eq21102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159788
  have eq186832 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq22376 eq162827
    | (have j0 := eq162827 (σ x) X0
       grind)
    | exact resolve eq162827 eq22376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162827
  have eq188248 : ∀ X0 X1 : G, (M.op (k (M.op (σ x) (σ y)) (σ x)) (M.op X1 (σ x))) = X1 ∨ (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) X0)) := by
    intro X0 X1
    first
    | exact superpose eq186832 eq3644
    | (have j1 := eq186832 X0
       grind)
    | exact resolve eq3644 eq186832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3644 eq186832
  have eq190539 : ∀ X0 : G, (σ x) = (M.op (k (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq22376 eq188248
    | (have j0 := eq188248 X0 x
       grind)
    | exact resolve eq188248 eq22376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22376 eq188248
  have eq191491 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (k (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq190539 eq22388
    | exact resolve eq22388 eq190539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22388 eq190539
  have eq203257 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) X0)))))) ∨ (σ x) = (M.op (k (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq191491 eq58177
    | exact resolve eq58177 eq191491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58177 eq191491
  have eq203433 : (σ x) = (M.op (k (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq203257 x
       have i₂ := eq17434 sF4 sF2 x sF4
       grind)
    | (have i₁ := eq203257 x
       have i₂ := eq17434 x x x (M.op sF4 (M.op sF4 (M.op sF2 (M.op sF4 (M.op x (M.op sF2 x))))))
       grind)
    | exact superpose eq17434 eq203257
    | exact resolve eq203257 eq17434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17434 eq203257
  have eq204042 : ∀ X0 : G, (M.op (M.op (k (M.op (σ x) (σ y)) (σ x)) X0) (M.op (M.op x (M.op (M.op (σ x) (σ y)) (M.op x (M.op x y)))) (σ x))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq203433 eq77163
    | exact resolve eq77163 eq203433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77163 eq203433
  have eq204049 : ∀ X0 : G, (M.op (M.op (k (M.op (σ x) (σ y)) (σ x)) X0) (M.op (M.op (σ x) (σ y)) (M.op x (M.op (σ x) (M.op x (M.op x y)))))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq21519 eq204042
    | exact resolve eq204042 eq21519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21519 eq204042
  have eq204133 : ∀ X0 : G, (M.op (M.op (k (M.op (σ x) (σ y)) (σ x)) X0) (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq22424 eq204049
    | exact resolve eq204049 eq22424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204049
  have eq204591 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) X1)) = (M.op X0 (M.op (M.op x (M.op (k (M.op (σ x) (σ y)) (σ x)) X0)) (M.op x (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f204591_13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (M.op X0 X2) (M.op (M.op x X0) (M.op x (M.op x y)))) := by
      intro X0 X1 X2
      grind
    have f204591_14 : ∀ X0 : G, (M.op (M.op (k (M.op (σ x) (σ y)) (σ x)) X0) (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f204591_23 : (M.op X1 (M.op (σ x) X1)) ≠ (M.op X0 (M.op (M.op x (M.op (k (M.op (σ x) (σ y)) (σ x)) X0)) (M.op x (M.op x y)))) := by grind
    have f204591_24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
    have f204591_25 : ∀ X0 : G, (M.op (M.op (k (M.op (σ x) (σ y)) (σ x)) X0) (σ x)) = X0 := by
      intro X0
      first
      | (have j0 := f204591_14 X0
         grind)
      | (have r₁ := f204591_14 X0
         have r₂ := f204591_24
         grind)
      | exact resolve f204591_14 f204591_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f204591_67 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) X1)) = (M.op X0 (M.op (M.op x (M.op (k (M.op (σ x) (σ y)) (σ x)) X0)) (M.op x (M.op x y)))) := by
      intro X0 X1
      first
      | (have i₁ := f204591_13 (M.op (k (M.op (σ x) (σ y)) (σ x)) X0) X1 (σ x)
         have i₂ := f204591_25 X0
         grind)
      | exact superpose f204591_25 f204591_13
      | exact resolve f204591_13 f204591_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f204591_69 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
      intro X0 X1 X2
      first
      | (have i₁ := f204591_13 x X0 X1
         have i₂ := f204591_13 x X2 X1
         grind)
      | exact superpose f204591_13 f204591_13
      | exact resolve f204591_13 f204591_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f204591_15674 : ∀ X0 : G, (M.op X1 (M.op (σ x) X1)) ≠ (M.op X0 (M.op (σ x) X0)) := by
      intro X0
      first
      | (have i₁ := f204591_23
         have i₂ := f204591_67 X0 X0
         grind)
      | exact superpose f204591_67 f204591_23
      | (have r₁ := f204591_23
         have r₂ := f204591_67 X0 X1
         grind)
      | exact resolve f204591_23 f204591_67
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f204591_15675 : False := by
      first
      | (have r₁ := f204591_15674 x
         have r₂ := f204591_69 X1 (σ x) x
         grind)
      | (have r₁ := f204591_15674 x
         have r₂ := f204591_69 x (σ x) X1
         grind)
      | exact resolve f204591_15674 f204591_69
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f204591_15675
  clear eq21112 eq204133
  have eq204653 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) X1)) = (M.op X0 (M.op (k (M.op (σ x) (σ y)) (σ x)) (M.op x (M.op X0 (M.op x (M.op x y)))))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq21140 eq204591
    | exact resolve eq204591 eq21140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204591
  have eq204726 : ∀ X1 : G, (M.op X1 (M.op (σ x) X1)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq21084 eq204653
    | exact resolve eq204653 eq21084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204653
  have eq205287 : ∀ X0 : G, (k (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 (M.op (σ x) X0)) (M.op x (M.op (M.op (σ x) (σ y)) (M.op x (M.op x y))))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq22419 eq204726
    | exact resolve eq204726 eq22419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22419 eq204726
  have eq205775 : (k (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21102 eq205287
    | exact resolve eq205287 eq21102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205287
  have eq205845 : (k (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have j1 := eq22988 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq205775
       have r₂ := eq22988 x
       grind)
    | exact resolve eq205775 eq22988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22988 eq205775
  have eq205866 : (M.op (M.op x y) (M.op (σ x) (M.op x y))) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq22377 eq205845
    | exact resolve eq205845 eq22377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22377 eq205845
  have eq210990 : (τ (M.op (M.op x y) (M.op (σ x) (M.op x y)))) = (k (τ (M.op (σ x) (σ y))) (τ (σ x))) := by
    first
    | exact superpose eq205866 eq136
    | exact resolve eq136 eq205866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq205866
  have eq211003 : (k (τ (M.op (σ x) (σ y))) x) = (τ (M.op (M.op x y) (M.op (σ x) (M.op x y)))) := by
    first
    | exact superpose eq38 eq210990
    | exact resolve eq210990 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210990
  have eq211008 : ∀ X0 : G, (k (τ (M.op (σ x) (σ y))) x) = (τ (M.op X0 (M.op (σ x) X0))) := by
    intro X0
    first
    | (have i₁ := eq211003
       have i₂ := eq1476 sF0 sF2 x
       grind)
    | (have i₁ := eq211003
       have i₂ := eq1476 X0 sF2 sF0
       grind)
    | exact superpose eq1476 eq211003
    | exact resolve eq211003 eq1476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1476 eq211003
  have eq295650 : ∀ X0 : G, (σ (τ X0)) = (k (M.op X0 (M.op x (M.op x (M.op x (M.op x y))))) (σ (τ x))) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq50924 eq49
    | (have j1 := eq50924 X0
       grind)
    | exact resolve eq49 eq50924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq50924
  have eq295652 : ∀ X0 : G, (σ (τ X0)) = (k (M.op X0 (M.op x (M.op x (M.op x (M.op x y))))) x) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have i₁ := eq295650 X0
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq295650
    | (have j0 := eq295650 X0
       grind)
    | exact resolve eq295650 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295650
  have eq295658 : ∀ X0 : G, (k (M.op X0 (M.op x (M.op x (M.op x (M.op x y))))) x) = X0 ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have i₁ := eq295652 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq295652
    | (have j0 := eq295652 X0
       grind)
    | exact resolve eq295652 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295652
  have eq295673 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k (M.op X0 x) x) ∨ (M.op x y) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq21102 eq295658
    | (have j0 := eq295658 (M.op X1 (M.op X0 X1))
       grind)
    | exact resolve eq295658 eq21102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21102 eq295658
  have eq296109 : ∀ X0 X1 : G, (M.op x y) ≠ (k (M.op X0 x) x) ∨ x = (M.op x y) ∨ x = (k (M.op X0 x) x) ∨ (M.op x y) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24008 X1 X0
       have i₂ := eq295673 X0 X1
       grind)
    | exact superpose eq295673 eq24008
    | (have j0 := eq24008 X0 X0
       have j1 := eq295673 X0 X1
       grind)
    | (have r₁ := eq24008 X1 X0
       have r₂ := eq295673 X0 X1
       grind)
    | exact resolve eq24008 eq295673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq296137 : ∀ X0 : G, (M.op x (M.op x y)) = (k (M.op x x) x) ∨ (M.op x y) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq20995 X0
       have i₂ := eq295673 x X0
       grind)
    | exact superpose eq295673 eq20995
    | (have j1 := eq295673 x X0
       grind)
    | exact resolve eq20995 eq295673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295673
  have eq296370 : ∀ X0 : G, (k (M.op x y) x) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq296137 X0
       have i₂ := eq20956
       grind)
    | exact superpose eq20956 eq296137
    | (have j0 := eq296137 X0
       grind)
    | exact resolve eq296137 eq20956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296137
  have eq296373 : ∀ X0 : G, (M.op x y) ≠ (k (M.op X0 x) x) ∨ x = (M.op x y) ∨ x = (k (M.op X0 x) x) := by
    intro X0
    first
    | (have j0 := eq296109 X0 x
       have j1 := eq24008 X0 X0
       grind)
    | (have r₁ := eq296109 x X0
       have r₂ := eq24008 X0 x
       grind)
    | exact resolve eq296109 eq24008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24008 eq296109
  have eq296695 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op x (M.op x y)))) = X0 ∨ (k (M.op x y) x) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq21121 x X0
       have i₂ := eq296370 x
       grind)
    | exact superpose eq296370 eq21121
    | exact resolve eq21121 eq296370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21121 eq296370
  have eq298828 : ∀ X0 : G, (M.op (M.op x (M.op x y)) (M.op x y)) = (M.op x (M.op (M.op X0 (M.op x (M.op x y))) X0)) ∨ (k (M.op x y) x) = (M.op x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq296695 eq22334
    | exact resolve eq22334 eq296695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22334 eq296695
  have eq298853 : ∀ X0 : G, (M.op (M.op x (M.op x y)) (M.op x y)) = (M.op (M.op x (M.op x y)) (M.op (M.op X0 x) X0)) ∨ (k (M.op x y) x) = (M.op x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq27790 eq298828
    | exact resolve eq298828 eq27790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27790 eq298828
  have eq298894 : (M.op (M.op x (M.op x y)) (M.op x y)) = (M.op (M.op x (M.op x y)) (M.op x (M.op x (M.op x (M.op x y))))) ∨ (k (M.op x y) x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq298853 x
       have i₂ := eq21015 x x
       grind)
    | exact superpose eq21015 eq298853
    | exact resolve eq298853 eq21015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21015 eq298853
  have eq298907 : (M.op x y) = (M.op (M.op x (M.op x y)) (M.op x y)) ∨ (k (M.op x y) x) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq21013 eq298894
    | exact resolve eq298894 eq21013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298894
  have eq298912 : x = (M.op x y) ∨ (k (M.op x y) x) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq22981 eq298907
    | exact resolve eq298907 eq22981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22981 eq298907
  have eq298913 : (k (M.op x y) x) = (M.op x (M.op x y)) := by
    first
    | (have j1 := eq22956 (M.op x y)
       grind)
    | (have r₁ := eq298912
       have r₂ := eq22956 x
       grind)
    | exact resolve eq298912 eq22956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298912
  have eq298916 : (M.op (σ x) (σ (M.op x y))) = (σ (M.op x (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq298913 eq22911
    | exact resolve eq22911 eq298913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22911 eq298913
  have eq301477 : ∀ X0 : G, (M.op (σ x) (σ (M.op x y))) = (σ (M.op X0 (M.op x X0))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20995 eq298916
    | exact resolve eq298916 eq20995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20995 eq298916
  have eq302391 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (τ (M.op (σ x) (σ (M.op x y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 (M.op x X0))
       have i₂ := eq301477 X0
       grind)
    | exact superpose eq301477 eq10
    | exact resolve eq10 eq301477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301477
  have eq302837 : ∀ X0 X1 : G, (M.op (M.op (τ (M.op (σ x) (σ (M.op x y)))) X1) (M.op X0 (M.op (M.op x (M.op x X0)) (M.op x (M.op x y))))) = X1 ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq22084 (M.op x X0) X0 X1
       have i₂ := eq302391 X0
       grind)
    | exact superpose eq302391 eq22084
    | exact resolve eq22084 eq302391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22084 eq302391
  have eq302970 : ∀ X0 X1 : G, (M.op (M.op (τ (M.op (σ x) (σ (M.op x y)))) X1) (M.op X0 (M.op x (M.op x (M.op X0 (M.op x (M.op x y))))))) = X1 ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq21140 eq302837
    | exact resolve eq302837 eq21140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21140 eq302837
  have eq303095 : ∀ X1 : G, (M.op (M.op (τ (M.op (σ x) (σ (M.op x y)))) X1) x) = X1 ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    intro X1
    first
    | exact superpose eq21084 eq302970
    | exact resolve eq302970 eq21084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21084 eq302970
  have eq309539 : ∀ X0 : G, (M.op x y) ≠ (k X0 x) ∨ x = (M.op x y) ∨ x = (k X0 x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq303095 eq296373
    | exact resolve eq296373 eq303095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296373 eq303095
  have eq330888 : ∀ X0 : G, (τ X0) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (τ X0) = x ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq29649 eq309539
    | (have j1 := eq29649 (M.op (σ x) (σ (M.op x y)))
       grind)
    | exact resolve eq309539 eq29649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29649 eq309539
  have eq365341 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op X3 (M.op (M.op x (M.op x (M.op x y))) X0)) (M.op X1 (M.op X3 (M.op (M.op x y) X0)))))) = X2 := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq23847 eq58166
    | exact resolve eq58166 eq23847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23847 eq58166
  have eq416091 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37 eq330888
    | (have j0 := eq330888 (M.op (σ x) (σ (M.op x y)))
       grind)
    | (have r₁ := eq330888 (σ (M.op x y))
       have r₂ := eq37
       grind)
    | exact resolve eq330888 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330888
  have eq416092 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq416091
  have eq416093 : x = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq416092
  have eq416094 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq416093
       have r₂ := eq27
       grind)
    | exact resolve eq416093 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416093
  have eq416186 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op x (M.op (σ x) (M.op x (M.op x y))))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq416094 eq21013
    | exact resolve eq21013 eq416094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21013 eq416094
  have eq416378 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22424 eq416186
    | exact resolve eq416186 eq22424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22424 eq416186
  have eq416420 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq416378 eq38
    | exact resolve eq38 eq416378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq416378
  have eq417037 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq416420
    | exact resolve eq416420 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416420
  have eq417038 : x = (M.op x y) := by grind
  clear eq417037
  have eq417041 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq417038 eq20
    | exact resolve eq20 eq417038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq417044 : x = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq417038 eq37
    | exact resolve eq37 eq417038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq417674 : x = (M.op x x) := by
    first
    | exact superpose eq417038 eq20956
    | exact resolve eq20956 eq417038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20956
  have eq417899 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq417038 eq22956
    | (have j0 := eq22956 X0
       grind)
    | (have r₁ := eq22956 X0
       have r₂ := eq417038
       grind)
    | exact resolve eq22956 eq417038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22956
  have eq433913 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op X3 (M.op (M.op x (M.op x x)) X0)) (M.op X1 (M.op X3 (M.op x X0)))))) = X2 := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq417038 eq365341
    | exact resolve eq365341 eq417038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365341 eq417038
  have eq434361 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq417899 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417899
  have eq434501 : ∀ X1 X2 : G, (M.op X1 (M.op X2 X1)) = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq433913 x X1 X2 x
       have i₂ := eq17032 x x x x X1
       grind)
    | exact superpose eq17032 eq433913
    | exact resolve eq433913 eq17032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17032 eq433913
  have eq441292 : ∀ X0 : G, (τ (M.op X0 (M.op (σ x) X0))) = (M.op x (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq211008 X0
       have i₂ := eq434361 (τ sF4)
       grind)
    | exact superpose eq434361 eq211008
    | exact resolve eq211008 eq434361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211008 eq434361
  have eq445369 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq417041
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq417041
    | exact resolve eq417041 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417041
  have eq451584 : (τ (σ x)) = (M.op x (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq441292 x
       have i₂ := eq434501 x sF2
       grind)
    | (have i₁ := eq441292 x
       have i₂ := eq434501 x (M.op x (M.op sF2 x))
       grind)
    | exact superpose eq434501 eq441292
    | exact resolve eq441292 eq434501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441292
  have eq455056 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq445369 eq22
    | exact resolve eq22 eq445369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq463940 : (τ (σ (M.op x y))) = (M.op x (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq445369 eq451584
    | exact resolve eq451584 eq445369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445369 eq451584
  have eq472961 : x = (M.op x (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq417044 eq463940
    | exact resolve eq463940 eq417044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417044 eq463940
  have eq481487 : x = (M.op (τ (M.op (σ x) (σ y))) x) := by
    first
    | exact superpose eq472961 eq434501
    | exact resolve eq434501 eq472961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472961
  have eq481843 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq481487 eq434501
    | exact resolve eq434501 eq481487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434501 eq481487
  have eq481844 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq481843
       have i₂ := eq417674
       grind)
    | exact superpose eq417674 eq481843
    | exact resolve eq481843 eq417674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417674 eq481843
  have eq481888 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq481844 eq11
    | exact resolve eq11 eq481844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481844
  have eq482025 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq481888
       have i₂ := eq455056
       grind)
    | exact superpose eq455056 eq481888
    | exact resolve eq481888 eq455056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455056 eq481888
  have eq482056 : False := by grind
  exact eq482056
